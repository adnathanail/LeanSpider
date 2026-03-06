# ZxLean

Lean 4 project for ZX-calculus diagrams with interactive visualization via ProofWidgets.

## Project structure

- `ZxLean/` — Lean 4 library: ZX diagram types, spider fusion, JSON serialization
- `zx_view_widget/` — TypeScript ProofWidgets widget (React, rollup). Sends diagram JSON to pyzx_daemon, displays rendered PNG in VS Code InfoView
- `pyzx_daemon/` — Python Flask server (managed with `uv`). Converts ZxLean JSON → pyzx Graph, renders with matplotlib, returns base64 PNG
- `Main.lean` — Entry point with example diagrams shown in InfoView

## Build commands

```sh
lake build
```

The Python daemon starts automatically when `ZxLean.Visualize` is imported (via an `initialize` block). Logs are written to `pyzx_daemon/pyzx_daemon.log`.

## Key conventions

- `ZXDiagram` uses `Std.HashMap NodeId Node` with a monotonic `nextId` counter for stable node IDs. Node IDs persist across additions and removals (no reindexing).
- Construct diagrams with `ZXDiagram.ofArrays` (array indices become IDs) or `ZXDiagram.addNode`/`ZXDiagram.addEdge`
- Look up nodes with `d.getNode? id`, not array indexing
- ZXDiagram nodes: `.input ioId`, `.output ioId`, `.spider color phase` where phase is a `Phase` (num/den)
- JSON wire format between widget and daemon: `{"nodes": [...], "edges": [{"src": id, "tgt": id}]}`
- Daemon host/port/URL config constants live in `ZxLean/Visualize.lean` (`daemonHost`, `daemonPort`, `daemonUrl`) — this is the single source of truth, passed to both the Python daemon (via CLI args) and the TypeScript widget (via props)
- Daemon runs on `127.0.0.1:5050`
- Python requires `>=3.14`, uses `uv` for dependency management (not pip)

## Lean tips

- `ZXDiagram` has no `Inhabited` instance — use `.getD` with a fallback (not `.get!`) when unwrapping `Option ZXDiagram`
- `Std.HashMap` doesn't support `deriving Repr` or `deriving BEq` — `ZXDiagram` has manual instances
