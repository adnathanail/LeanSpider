# LeanZX

Lean 4 project for ZX-calculus diagrams with interactive visualization via ProofWidgets.

## Project structure

- `LeanZX/` — Lean 4 library: ZX diagram types, spider fusion, JSON serialization
- `zx_view_widget/` — TypeScript ProofWidgets widget (React, rollup). Runs pyzx inside the InfoView via Pyodide (CPython compiled to WASM), renders the diagram as a PNG and displays it.
- `Main.lean` — Entry point with example diagrams shown in InfoView

## Build commands

```sh
lake build
```

The JS bundle (~16MB) is built by rollup and written to `.lake/build/js/`. It embeds the Pyodide runtime (WASM + stdlib) at build time so no network access is needed to start pyodide. Python packages (pyzx, numpy, networkx, matplotlib and their deps) are fetched from CDN/PyPI on first widget render and cached by the browser.

## Key conventions

- `ZXDiagram` uses `Std.HashMap NodeId Node` with a monotonic `nextId` counter for stable node IDs. Node IDs persist across additions and removals (no reindexing).
- Construct diagrams with `ZXDiagram.ofArrays` (array indices become IDs) or `ZXDiagram.addNode`/`ZXDiagram.addEdge`
- Look up nodes with `d.getNode? id`, not array indexing
- ZXDiagram nodes: `.input ioId`, `.output ioId`, `.spider color phase`, `.hadamard phase` where phase is a `Phase` (num/den)
- JSON wire format from Lean to the widget: `{"nodes": [...], "edges": [{"src": id, "tgt": id}]}`
- Python rendering logic lives in `zx_view_widget/src/zxRender.py` — edit this file to change how diagrams are drawn. Lake tracks `.py` files and rebuilds the widget when they change.

## Widget architecture

The widget (`zx_view_widget/src/zxDiagram.tsx`) loads Pyodide as follows:
1. At rollup build time, `pyodide.asm.wasm`, `pyodide.asm.js`, `python_stdlib.zip`, and `pyodide-lock.json` are embedded into the JS bundle as base64 data URLs via a custom rollup plugin (`pyodideBundled` in `rollup.config.js`).
2. At runtime, the widget evals `pyodide.asm.js` to set `_createPyodideModule` globally (skipping pyodide's dynamic import), patches `globalThis.fetch` to serve the bundled WASM and stdlib from memory, then calls `loadPyodide`. The fetch patch is restored once `loadPyodide` returns.
3. After pyodide loads, `micropip` installs `pyzx==0.10.0`, `lark==1.3.1`, and `pyperclip==1.11.0` from PyPI. `numpy`, `networkx`, `matplotlib`, `tqdm`, and `typing-extensions` are loaded from pyodide's CDN.
4. `zxRender.py` is executed to define the `render(diagram_json)` function, which converts the Lean JSON to a pyzx graph and returns a base64 PNG.

## Lean tips

- `ZXDiagram` has no `Inhabited` instance — use `.getD` with a fallback (not `.get!`) when unwrapping `Option ZXDiagram`
- `Std.HashMap` doesn't support `deriving Repr` or `deriving BEq` — `ZXDiagram` has manual instances
