# LeanSpider

Lean 4 project for ZX-calculus diagrams with interactive visualization via ProofWidgets.

## Committing

Sometimes this repository is managed with GitButler.
Check whether you are on the `gitbutler/workspace` branch; if so, use the `but` CLI to interact with it.
Make changes in new commits, as opposed to modifying existing commits, unless explicitly told to.

**Do not add attributions to yourself in commit messages**

## Project structure

- `LeanSpider/` — Lean 4 library: ZX diagram types, spider fusion, JSON serialization. `Tactics.lean` holds the rewrite tactics, `Panel.lean` the InfoView panel widget and expression presenter.
- `zx_view_widget/` — TypeScript ProofWidgets widget (React, rollup). A thin shell that hands the Lean diagram JSON to the `<zx-diagram>` web component from [`@adnathanail/zxcc`](https://www.npmjs.com/package/@adnathanail/zxcc), which does the layout and SVG rendering.
- `Main.lean` — Entry point with example diagrams shown in InfoView

## Build commands

```sh
lake build
```

The JS bundle is built by rollup and written to `.lake/build/js/`. zxcc is bundled at build time; there are no runtime network requests.

## Key conventions

- `ZXDiagram` uses `List (Option Node)` for nodes (list indices are node IDs) and `List Edge` for edges.
- Construct diagrams with `ZXDiagram.ofList` (list indices become IDs) or `ZXDiagram.addNode`/`ZXDiagram.addEdge`
- Look up nodes with `d.getNode? id`, not direct list indexing
- ZXDiagram nodes: `.input ioId`, `.output ioId`, `.spider color phase`, `.hadamard`, `.wire` where phase is a `Phase` (`num : Int`, `den : ℕ+`)
- Phases cross the wire as display-ready strings (`π/2`, `-π/4`, `0`) — `Phase.format` in `LeanSpider/Visualize.lean` is the single source of truth; the widget prints them verbatim
- JSON wire format from Lean to the widget: `{"nodes": [...], "edges": [{"src": id, "tgt": id}]}`
- Layout and rendering both live in the separate [zxcc](https://github.com/adnathanail/zxcc) repo, not here — change them there and release a new version.
- Demo diagrams live in `LeanSpider.Examples`, not the root namespace, so that `open LeanSpider` doesn't take names like `cnot` out of a user's hands. Keep new example data there.

## Rewrite tactics

`applyRewrite` in `LeanSpider/Tactics.lean` reduces a rule application with `whnf`, which exposes the `Except.ok` head but leaves the diagram's fields unevaluated. It then evaluates that diagram with `evalZXDiagram` and reflects the value back into an `Expr` with `reflectDiagram`, so the goal holds a flat literal rather than an application tree that grows with each tactic line.

`reflectDiagram`/`reflectNode`/`reflectPhase` mirror the `Node` and `Phase` definitions by hand and must be updated alongside them — a new constructor or field will otherwise reflect wrongly or fail to compile. They are `MetaM` rather than a `ToExpr` instance because an `ℕ+` denominator needs `mkNumeral` to synthesize its `OfNat` instance; that synthesis is cached per distinct denominator, since repeating it per phase measurably slows elaboration.

## Goal display for diagram literals

`LeanSpider/Delab.lean` delaborates reflected diagrams so the node list reads `[Node.input 0, _, Node.hadamard]` instead of being buried in `some`/`none`. Three things about it are deliberate:

- It is registered on `ZXDiagram.mk`, not on `Option.some`. Delaborators dispatch on head symbol, so unwrapping `some` directly would hide it for every `Option` in every goal in the file.
- An empty slot prints as `_` rather than being dropped. Node IDs are list indices, so removing empties would renumber every node after them, and those IDs are what get typed into `zx_sp 1 3`.
- The placeholder is a hole and **not** `·`, which reads better but cannot be used: declaring `syntax "·" : term` collides with Lean's cdot parser and breaks `(· + 1)` in every file that imports this library. If you want a different glyph, pick one outside Lean's grammar.

`delabNodeList` fails on anything not built from `cons`/`nil`, so a diagram over variables (`{ nodes := xs, edges := ys }`) falls back to the default display instead of rendering something misleading. Keep that guard.

## Widget architecture

`zx_view_widget/src/zxDiagram.tsx` handles only the InfoView shell: the LHS/RHS side-by-side layout and its persisted toggle. For each panel it renders a `<zx-diagram>` element and assigns the Lean JSON to its `.diagram` property; zxcc lays the graph out and draws the interactive SVG. Nodes are draggable, H-boxes auto-position at the barycenter of their neighbours, and parallel edges are drawn as bezier arcs.

## Displaying diagrams in the InfoView

Diagrams reach the InfoView two ways, both defined in `LeanSpider/Panel.lean`:

- **`ZXPanel`** — a panel widget (`mk_rpc_widget%` over `ZXPanel.rpc`) that reads the main goal and renders a `d₁ ≈z d₂` goal as LHS and RHS side by side. Enable it per section with `show_panel_widgets [local ZXPanel]`, or per proof with `with_panel_widgets [ZXPanel]`. It tracks the cursor, so every step of a proof displays its own diagram with no tactic call.
- **`zxPresenter`** — an `@[expr_presenter]` covering both a `≈z` goal and a bare `ZXDiagram` term. ProofWidgets' `SelectionPanel` uses it to render subterms shift-clicked in the tactic state; `GoalTypePanel` uses it to render the goal type. Enable either the same way, e.g. `show_panel_widgets [local ProofWidgets.SelectionPanel]`.

Outside a proof, the `#zx d` command (also in `Panel.lean`) renders a diagram. It elaborates its argument at type `ZXDiagram`, so a wrong argument gives an ordinary Lean type error. Use it rather than ProofWidgets' `#html`.

Both paths evaluate the `Expr` to a real `ZXDiagram` via `evalZXDiagram` (`Meta.evalExpr`), so they need closed terms. On a goal with free variables or an unassigned metavariable LHS, `ZXPanel` shows "No ZX diagram" and `zxPresenter` throws — which is how `getExprPresentations` knows to omit it. A presenter that cannot render **must** throw rather than return empty HTML.

Tactics do not log diagrams. `zx_debug` is the one tactic that writes to the InfoView, printing raw diagram JSON (`includeNones := true`) for debugging.

## Lean tips

- `ZXDiagram` has a manual `BEq` instance that sorts edges before comparison, so edge order doesn't affect equality
