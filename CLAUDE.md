# SpLean

Lean 4 project for ZX-calculus diagrams with interactive visualization via ProofWidgets.

`SpLean/Axiomatic/` is a sort of 'reference implementation', not fully complete in terms of desired functionality, but showing the level of ergonomics we hope to be able to achieve in terms of writing proofs.

`SpLean/Algebraic/` is the main focus now, trying to create fully proven methods to work with ZX diagrams in Lean.

## Committing

Sometimes this repository is managed with GitButler.
Check whether you are on the `gitbutler/workspace` branch; if so, use the `but` CLI to interact with it.
Make changes in new commits, as opposed to modifying existing commits, unless explicitly told to.

**Do not add attributions to yourself in commit messages**

## Writing style

When writing comments, or user facing text, write from the context of someone coming into the context cold.
Don't write as though someone has heard the conversation.
People don't need to know that something hasn't happened.

If that sort of design decision context is important, put it in CLAUDE.md

## Project structure

- `SpLean/` — Lean 4 library, split into one folder per representation plus the little that is genuinely shared:
  - `Widget.lean` — the zxcc **wire format** (`SpLean.Wire`: `NodeKind`, `Node`, `Edge`, `BoxKind`, `Box`, `Diagram`, `toJson`) and the ProofWidgets `ZXWidget` that eats it. A pure data-transfer type: no `Phase`, no `SpiderColor`, phases already display strings.
  - `Panel.lean` — the InfoView panel widget, expression presenter, and `#zx` command. The one file that knows both representations: it holds no rendering of its own, only the dispatch between `Axiomatic/Render.lean` and `Algebraic/Render.lean`.
  - `Axiomatic/` — the graph-based approach: `ZXDiagram.lean` (`SpiderColor`, `Phase`, `Node`, `Edge`, `ZXDiagram` + graph ops), `Visualize.lean` (`ZXDiagram → Wire.Diagram`), `Render.lean` (`Expr → Html`), `Axioms.lean` (`≈z`), `Tactics.lean` (the rewrite tactics), `Rules/`, `DerivedRules/`, `Examples.lean`.
  - `Algebraic/` — the arity-indexed `ZX n m` approach, with its own spider colour (`AlgSpColor`), phase type and renderer, plus the denotational semantics (`Semantics.lean`), the proportionality equivalence (`Equiv.lean`), the rules proved against it (`Rules/`), the `zx_rw` tactic (`Tactics.lean`), arity-casting for it (`Cast.lean`) and derived diagram combinators (`Combinators.lean`: `nStack`/`nWire`/`nHadamard`/cup/cap) and a few named gates (`Gate.lean`); see `SpLean/Algebraic/CLAUDE.md`.
  - `Utils.lean` — generic `List`/`Except`/`Option` helpers. `All.lean` imports everything.

  **`Axiomatic/` and `Algebraic/` import nothing from each other** — check with `grep -rh "^import" SpLean/Algebraic/`. They meet at `SpLean.Wire` and at `Panel.lean`, and nowhere else. The spider colour is deliberately defined twice rather than shared — `SpiderColor` in `Axiomatic/`, `AlgSpColor` in `Algebraic/` — since two three-line types are cheaper than an arrow between the halves. They are named apart so neither has to be identified by its namespace.
  **This is not a strict rule, it's just nice to have for now**
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
- Phases become display-ready strings *before* reaching the wire format, and the widget prints them verbatim. Each representation formats its own: `Phase.format` (`Axiomatic/Visualize.lean`, normalizes mod 2π) and `AlgPhase.format` (`Algebraic/AlgPhase/Display.lean`, deliberately does not). A symbolic phase is just the pretty-printed phase argument in the same field.
- JSON wire format: written down once, in `SpLean/Widget.lean`, as `Wire.Diagram.toJson`. `{"nodes": [...], "edges": [{"src", "tgt"}]}`, with each node carrying `id`/`type` and whichever of `color`/`phase`/`ioId`/`col`/`qubit` apply — an `Option` that is `none` is *omitted*, not sent as null. Algebraic terms fill in `col`/`qubit` (which makes zxcc skip its own layout) and add a top-level `boxes` array of `{kind, nodeIds}`. Changing what the wire looks like means changing that one file and the two lowerings into it.
- Layout and rendering both live in the separate [zxcc](https://github.com/adnathanail/zxcc) repo, not here — change them there and release a new version.
- Demo diagrams live in `SpLean.Examples` (`SpLean/Axiomatic/Examples.lean`), not the root namespace, so that `open SpLean` doesn't take names like `cnot` out of a user's hands. Keep new example data there.

## Rewrite tactics

The two representations rewrite by completely different mechanisms: `≈z` is decided by evaluating diagrams, `≈zx` by `grw` over a proved relation. Neither tactic works on the other's goals.

### Axiomatic (`≈z`)

`applyRewrite` in `SpLean/Axiomatic/Tactics.lean` reduces a rule application with `whnf`, which exposes the `Except.ok` head but leaves the diagram's fields unevaluated. It then evaluates that diagram with `evalZXDiagram` and reflects the value back into an `Expr` with `reflectDiagram`, so the goal holds a flat literal rather than an application tree that grows with each tactic line.

`reflectDiagram`/`reflectNode`/`reflectPhase` mirror the `Node` and `Phase` definitions by hand and must be updated alongside them — a new constructor or field will otherwise reflect wrongly or fail to compile. They are `MetaM` rather than a `ToExpr` instance because an `ℕ+` denominator needs `mkNumeral` to synthesize its `OfNat` instance; that synthesis is cached per distinct denominator, since repeating it per phase measurably slows elaboration.

### Algebraic (`≈zx`)

`zx_rw` in `SpLean/Algebraic/Tactics.lean` is `rw` for `≈zx` rules — `zx_rw [spider_fusion_Z_one_wire]`, `zx_rw [← spider_fusion_Z_one_wire]` to unfuse. It is a thin macro over Mathlib's `grw`, which generalises `rw` to any relation that is reflexive, transitive and has congruence lemmas; `≈zx` supplies all three (`ZX.Equiv.refl` is `@[refl]`, and `compose_congr`/`stack_congr` are tagged `@[gcongr]` in `Tactics.lean` rather than at their definitions, to keep the `grw` import out of `Equiv.lean`). The `@[gcongr]` tags are what let a rule fire *inside* a larger diagram rather than only at the top.

`nth_zx_rw 2 [colour_change_Z_X_one_wire]` is the `nth_rw` of the pair — same rules, same `zx_phase` pass, but firing only at the listed occurrences (`nth_zx_rw 1 3 [...]` for several). It expands to `grw (occs := .pos [...])` rather than to Mathlib's `nth_grw`, since a `(num)+` cannot be spliced back into `nth_grw`'s own syntax from a macro. Needed as soon as a rule's RHS contains its LHS's shape again — colour change on a diagram with several spiders, where plain `zx_rw` rewrites all of them.

Each goal `grw` leaves then gets a `zx_phase` pass, which normalises the phase arithmetic a rewrite produces — fusion outputs `α + β`, so `π/4 ≫ π/4` lands as `π/4 + π/4` where the goal says `π/2`. `zx_phase` pushes the `AlgPhase`s together with `← AlgPhase.ofRat_add`, hands the rational arithmetic to `norm_num`, and closes with `rfl` (which works on `≈zx` because of the `@[refl]`). It is kept behind `done`, so a goal it cannot close is handed back exactly as `grw` left it rather than half-normalised.

## Widget architecture

`zx_view_widget/src/zxDiagram.tsx` handles only the InfoView shell: the LHS/RHS side-by-side layout and its persisted toggle. For each panel it renders a `<zx-diagram>` element and assigns the Lean JSON to its `.diagram` property; zxcc lays the graph out and draws the interactive SVG. Nodes are draggable, H-boxes auto-position at the barycenter of their neighbours, and parallel edges are drawn as bezier arcs.

## Displaying diagrams in the InfoView

Diagrams reach the InfoView two ways, both defined in `SpLean/Panel.lean`:

- **`ZXPanel`** — a panel widget (`mk_rpc_widget%` over `ZXPanel.rpc`) that reads the main goal and renders an equivalence goal — graph-style `d₁ ≈z d₂` or algebraic `a ≈zx b` — as LHS and RHS side by side. Enable it per section with `show_panel_widgets [local ZXPanel]`, or per proof with `with_panel_widgets [ZXPanel]`. It tracks the cursor, so every step of a proof displays its own diagram with no tactic call.
- **`zxPresenter`** — an `@[expr_presenter]` covering an equivalence goal in either representation (`≈z`, `≈zx`) and a bare term in either (`ZXDiagram`, `ZX n m`). ProofWidgets' `SelectionPanel` uses it to render subterms shift-clicked in the tactic state; `GoalTypePanel` uses it to render the goal type. Enable either the same way, e.g. `show_panel_widgets [local ProofWidgets.SelectionPanel]`.

Outside a proof, the `#zx d` command (also in `Panel.lean`) renders a diagram. It takes either representation — a graph-style `ZXDiagram` or an algebraic `ZX n m` — and is the replacement for ProofWidgets' `#html d.toHtml`; the project has no remaining `#html` call sites. Because `ZX n m` is arity-indexed there is no single expected type to elaborate against, so the argument is elaborated with no expected type and the result dispatched on its type: notation that needs one (`.spider .Z 1 1`, anonymous constructors) has to be ascribed, e.g. `#zx (.spider .Z 1 1 : ZX 1 1)`. Anything else fails with an error naming the term's actual type. A `ZXDiagram` still has to be closed (it is evaluated); an algebraic term does not, and one with leading `∀`s over its phases is drawn with the binder names.

Each representation renders itself, in its own `Render.lean` — `Axiomatic/Render.lean` and `Algebraic/Render.lean`, both exposing a `zxEquivHtml?`. `ZXPanel` and `zxPresenter` go through `equivHtml?` in `Panel.lean`, which is only the dispatch between them: graph-style first, then algebraic. The two halves are drawn by opposite means, and it shows in what they accept:

- A `≈z` goal is *evaluated* — `evalZXDiagram` (`Meta.evalExpr`) — so both sides have to be closed. A goal with free variables or an unassigned metavariable LHS is not drawn.
- A `≈zx` goal is *walked* at the `Expr` level, so an open goal is fine: `α + β` on a spider is drawn as itself, which is what makes a mid-proof algebraic goal (`SemanticsTesting/09Rules.lean`) displayable. A side that is not built from the `ZX` constructors — an opaque `a : ZX 1 1` — is what cannot be drawn here.

Undrawable is not an error, but the renderers do not decide that: both return `none` only for "not this kind of expression at all" and *throw* on a term of the right shape they cannot draw. `softly` in `Panel.lean` is the single place that turns that into a `none` (letting interrupts and recursion-depth failures through, since neither is an answer about the diagram). It is also why `#zx` softens its `ZXDiagram` attempt — so an open one falls through to the error naming the type, rather than surfacing `evalExpr`'s complaint. `ZXPanel` then shows "No ZX diagram" and `zxPresenter` throws — which is how `getExprPresentations` knows to omit it. A presenter that cannot render **must** throw rather than return empty HTML.

Tactics do not log diagrams. `zx_debug` is the one tactic that writes to the InfoView, printing `ZXDiagram.debugJson` — which, unlike `toWire`, keeps the `none` slots left by `removeNode` as `{"id": i, "type": "none"}`, since where the holes are is what you want when debugging a rewrite. That JSON is never sent to the widget; `"none"` is not a zxcc node type.

## Two ZX representations

- **`ZXDiagram`** (`SpLean/Axiomatic/ZXDiagram.lean`) — graph-style: nodes + edges. Used by all rewrite rules in `Axiomatic/Rules/*` and the `≈z` equivalence. It used to sit in the shared root because the algebraic renderer lowered into it; it no longer does, so it lives with the rules that use it.
- **`ZX n m`** (`SpLean/Algebraic/ZX.lean`) — free-algebra ADT indexed by arity, with a denotational semantics (`ZX.sem`) and a proportionality equivalence `≈zx` proved against it. Spider fusion is *proved* here rather than axiomatised, and rewritten with `zx_rw`.

Both render through `SpLean.Wire`, by separate lowerings: `ZXDiagram.toWire` supplies no positions, so zxcc lays the graph out itself; `ZXSkel.toWire` supplies a `(col, qubit)` for every node from the algebraic structure — `compose` advances col, `stack` advances qubit; a `wire` stays a real `wire` node so the boxes around it are non-empty — so zxcc skips its layout. Each `stack`/`compose` subtree also records a bounding rectangle drawn behind the diagram. Algebraic terms are walked at the `Expr` level rather than evaluated, so a diagram parameterized by a phase (`(α : AlgPhase) → ZX 0 0`) renders with `α` written on the spider. See `SpLean/Algebraic/CLAUDE.md` for details.

## Lean tips

- `ZXDiagram` has a manual `BEq` instance that sorts edges before comparison, so edge order doesn't affect equality
