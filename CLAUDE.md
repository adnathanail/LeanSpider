# LeanSpider

Lean 4 project for ZX-calculus diagrams with interactive visualization via ProofWidgets.

## Project structure

- `LeanSpider/` — Lean 4 library: ZX diagram types, spider fusion, JSON serialization
- `zx_view_widget/` — TypeScript ProofWidgets widget (React, D3, rollup). Converts the Lean diagram JSON to a D3-compatible graph in TypeScript and renders it as an interactive D3 SVG.
- `Main.lean` — Entry point with example diagrams shown in InfoView

## Build commands

```sh
lake build
```

The JS bundle is built by rollup and written to `.lake/build/js/`. D3 v5 is bundled at build time; there are no runtime network requests.

## Key conventions

- `ZXDiagram` uses `List (Option Node)` for nodes (list indices are node IDs) and `List Edge` for edges.
- Construct diagrams with `ZXDiagram.ofList` (list indices become IDs) or `ZXDiagram.addNode`/`ZXDiagram.addEdge`
- Look up nodes with `d.getNode? id`, not direct list indexing
- ZXDiagram nodes: `.input ioId`, `.output ioId`, `.spider color phase`, `.hadamard` where phase is a `Phase` (num/den)
- JSON wire format from Lean to the widget: `{"nodes": [...], "edges": [{"src": id, "tgt": id}]}`
- Layout/conversion logic lives in `zx_view_widget/src/zxRender.ts` — edit this file to change graph layout. It is a TS port of pyzx's graph-construction + `graph_json` plus a small BFS layout.
- D3 rendering logic lives in `zx_view_widget/src/zxViewer.js` — vendored from pyzx's `zx_viewer.inline.js` with a fix for H-box edge redraw. Edit this file to change how the SVG is drawn.

## Widget architecture

The widget (`zx_view_widget/src/zxDiagram.tsx`) renders synchronously:
1. `zxRender.render(diagram)` (in `zxRender.ts`) walks the Lean diagram JSON, runs a BFS layout from inputs to assign rows/qubits, then emits a `{nodes, links}` object whose shape matches what `zxViewer.js` expects (per-node `t`/`phase`, per-link `index`/`num_parallel` for parallel-edge bezier arcs).
2. The widget passes that graph JSON to `showGraph()` from `zxViewer.js`, which renders an interactive SVG using D3 v5. Nodes are draggable, H-boxes auto-position at the barycenter of their neighbours, and parallel edges are drawn as bezier arcs.

## Two ZX representations

- **`ZXDiagram`** (`LeanSpider/ZXDiagram.lean`) — graph-style: nodes + edges. Used by all rewrite rules in `Rules/*` and the `≈z` equivalence.
- **`ZX n m`** (`LeanSpider/Algebraic/ZX.lean`) — free-algebra ADT indexed by arity, with denotational matrix semantics in `Algebraic/Semantics.lean`. Used to *prove* rules (rather than axiomatise them) — see `Algebraic/SpiderFusion.lean`.

Both are renderable in the InfoView: `ZXDiagram.toHtml` directly, `ZX.toHtml` via `ZX.toPositionedDiagram` (lowers to a graph and emits per-node `(col, qubit)` positions from the algebraic structure — `compose` advances col, `stack` advances qubit; `wire` is spliced into a plain edge). See `LeanSpider/Algebraic/CLAUDE.md` for details.

## Lean tips

- `ZXDiagram` has a manual `BEq` instance that sorts edges before comparison, so edge order doesn't affect equality
