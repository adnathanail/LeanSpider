# LeanSpider.Algebraic

A free-algebra ZX representation (`ZX n m`, indexed by input/output arity) with
a denotational interpretation into complex matrices over Mathlib. Lives
*alongside* the graph-style `ZXDiagram`. There is a one-way `ZX → ZXDiagram`
translation for **rendering only** (`Visualize.lean` — see below); the
`Rules/*` rewrite machinery still operates on `ZXDiagram` directly.

## Why this module exists

`LeanSpider/Axioms.lean` defines `≈z` as syntactic equality after compaction,
which is too weak to prove rewrite-rule soundness — every rewrite rule in
`LeanSpider/Rules/` is therefore axiomatised. This module gives a *semantic*
equivalence (`≃ZX` = matrix equality) so rewrite rules can be proven outright.
`Z_spiderFusion` in `SpiderFusion.lean` is the first such proof; its axiom
audit is `[propext, Classical.choice, Quot.sound]` only.

## Conventions

- **Composition order**: `compose a b` reads "first `a`, then `b`", so
  `⟦a × b⟧ = ⟦b⟧ * ⟦a⟧` (matrices act right-to-left).
- **Index convention**: `Matrix (Fin (2^m)) (Fin (2^n)) ℂ` — rows are outputs,
  columns are inputs. All-zeros basis vector at index `0`, all-ones at `2^k - 1`.
- **`Z_spiderMatrix` is a *sum* of two indicators, not nested `if`s.** Required
  for the `n = m = 0` corner case where both indices collide at `0` (a 0-leg
  spider is the scalar `1 + e^{iφ}`, not `1`).
- **`Phase.den : ℕ+`**, so `den = 0` is ruled out at the type level.
  `phaseToComplex_add` and the spider-fusion theorems carry no `den ≠ 0`
  hypothesis.

## Current placeholder semantics (deliberate, not `sorry`)

`ZX.sem` returns `0` for `hadamard`, `spider .X _ _ _`, and `stack _ _`. The
Z-spider-fusion proof never pattern-matches these branches, so they don't
affect its correctness — but **any new theorem touching H, X-spiders, or
tensor products needs real semantics first**:

- `stack`: Kronecker product with `Fin (2^(n+p)) ≃ Fin (2^n) × Fin (2^p)`
  reindexing (via `finProdFinEquiv` and `Nat.pow_add`).
- `spider .X`: Hadamard sandwich of the Z-spider — depends on `stack` for
  `H^⊗n`.
- `hadamard`: `![![1, 1], ![1, -1]] / √2`.

## Visualization (`Visualize.lean`)

`ZX.toHtml` renders an algebraic term in the existing `ZXWidget`. The walker
threads a private `Frag` (diagram + open `left`/`right` port lists, each port
paired with the qubit-in-halves at which it enters/leaves the body, +
`(width, height, pos, boxes)`) through the constructors. Every node carries
an algebraic-grid `(col, qubitHalves)` position emitted alongside the JSON,
so the widget skips its BFS layout and the visual reflects the term's
structure. Each `stack`/`compose` subtree also records a `BoxRecord` covering
its extent; the widget draws translucent rectangles behind the diagram so
the algebraic nesting is visible at a glance.

Qubit positions are stored internally as `2 ×` the actual qubit (i.e.
"halves") so a spider with mismatched arity (e.g. `Z 1→2`) can sit on a
half-row at the centre of its span. The structural `Frag.height` stays a
count of integer slots; `stack` shifts the lower fragment's qubits by
`2 * a.height`. JSON emission divides by two — `qubit` is a real number
(e.g. `0.5`, `1`, `1.5`) on the wire, and `zxRender.ts` already accepts
`qubit?: number` unchanged.

Per-constructor layout (all qubit values are halves; `centre = max(n, m) - 1`
is the midpoint of slots `0..max-1` in halves):

- `wire` → one `.wire` node at `(col 0, q 0)`, rendered by the widget as a
  small black dot (radius `0.2 * node_size`). Wires stay as real nodes so
  that `stack`/`compose` boxes around them are non-empty and the visual
  extent of a subtree matches its algebraic shape. `left = right = [(id, 0)]`,
  width 1, height 1.
- `hadamard` → one `.hadamard` node at `(col 0, q 0)`. `left = right = [(id, 0)]`,
  width 1, height 1.
- `spider c n m φ` → one node at `(col 0, q centre)` (centre of its span).
  Each port is paired with its qubitHalves: when the arity is `1` the lone
  port sits at `centre` (so a single-leg connection is horizontal); when
  arity > 1 the ports occupy integer slots `0, 2, …, 2(k-1)`. Width 1,
  height `max n m`.
- `stack a b` → concatenate; shift `b`'s qubitHalves by `2 * a.height`.
  Width `max a.width b.width`, height `a.height + b.height`.
- `compose a b` → connect `a.right` to `b.left` (by node id, qubits do not
  need to match) and shift `b`'s cols by `a.width`. Width `a.width + b.width`,
  height `max a.height b.height`.

`stack` and `compose` each emit a `BoxRecord {kind, nodeIds}` listing the ids
of every node in their subtree (with appropriate shifts on `compose`/`stack`).
Leaves emit no box. Pixel bounds are computed in `zxViewer.js` from each
node's live `.x/.y`, so boxes follow drags. Because wires are now real nodes
with positions, every subtree's bounding box extends exactly to its outermost
member — no overshoot, no live-id filter needed.

Boundary `.input`/`.output` nodes are added **only** at the top level by
`ZX.toPositionedDiagram`. Each boundary inherits the qubit of the body port
it connects to: input `i` sits at `(col -1, q (f.left[i].2))`, and output
`j` at `(col width, q (f.right[j].2))`. So a top-level input feeding a
`Z 1→2` spider lands on the spider's centred half-row, and an input feeding
a wire that has been pushed downward by a sibling stack lands at that wire's
shifted qubit — no big diagonal jumps from the boundary into the body.
Internal fragments stay arity-pure during recursion.

The JSON shape extends `ZXDiagram.toJson` with `col` (Int) and `qubit`
(real number, possibly half-integer) fields per node, plus a top-level
`boxes` array of `{kind, nodeIds}` records.
`zxRender.ts` honours the positions (skipping `autoLayout` whenever any node
has `col` set) and forwards boxes unchanged, sorted largest-id-count first
so outer paints behind inner. `zxViewer.js` accepts the box list as an extra
parameter to `showGraph`, renders them as the first `<g class="boxes">` child
of the SVG (with `pointer-events: none` so the brush layer still works), and
recomputes their bounds in `update_boxes()` after every drag tick. The
widget's `auto_hbox` flag is turned off in the positioned case, so hadamards'
supplied positions aren't overwritten by neighbour-barycentre repositioning.

`ZX.toZXDiagram` (used by callers that just need the graph) delegates to
`ZX.toPositionedDiagram` and discards the position list. Rendering-only —
there is no proof that the lowering preserves semantics (would need a
`ZXDiagram` denotation, which doesn't exist yet).

## Proof tactics that worked here

- For `Fin.sum_univ_two` over `Fin (2^1)`: use `show (∑ s : Fin 2, …)` to coerce
  the index type — the lemma won't unify against `Fin (2^1)` directly even
  though they're defeq.
- Collapsing `(if h₁ then a else 0) * (if h₂ then b else 0)` to a single
  AND-indicator: `simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, ← ite_and]`.
  Note `simp` happens to apply `mul_ite` first, which controls which condition
  ends up "outside" in the resulting AND.

## Rewrite infrastructure

`Rewrite.lean` and `Tactics.lean` provide a graph-style rewrite UX
parallel to what `LeanSpider/Tactics.lean` does for `ZXDiagram` —
pick two node IDs, apply a rule, get back a residual `≃ZX` goal.

- `ZX.nodeCount` (`Rewrite.lean`) mirrors `buildFrag`'s DFS counting
  exactly. Per-constructor contributions: `empty` 0; `wire`/`hadamard`/
  `spider` 1; `stack`/`compose` sum of children. Body nodes get IDs
  `0..count-1`; boundary inputs/outputs are added *after* the body in
  `ZX.toPositionedDiagram` so body IDs are stable.
- `ZX.applySpiderFusionAt` (`Rewrite.lean`) is the standalone
  computable rewrite — kept for future tactics or testing, but the
  live `zx_alg_fusion` tactic walks the term in MetaM directly
  (`buildFusionProof` in `Tactics.lean`).
- `zx_alg_fusion idA idB` (`Tactics.lean`): direct-compose only. Both
  spiders must be Z with arities `(_, 1)` and `(1, _)` and sit as the
  immediate children of one `compose`. The fused result has the *raw*
  phase sum (e.g. `⟨1,4⟩+⟨1,4⟩ = ⟨8,16⟩` via `Phase.add`, not the
  simplified `⟨1,2⟩`) — phase simplification stays a separate concern
  (use `spider_phase_eq` + `congr_phase`).

### Architecture (mirror of `applyRewrite`)

1. `parseAlgEquivGoal` extracts `(lhs, rhs)` from a goal
   `@ZX.equiv n m lhs rhs`. **Watch out:** `ZX.equiv` has two implicit
   index args (so 4 total), so `Expr.app2?` does *not* work — use
   `getAppFn`/`getAppArgs` and check `args.size == 4`.
2. `buildFusionProof` walks `lhs` DFS-style, threading an offset
   counter, returning `(lhs', proof : lhs ≃ZX lhs', endOffset)`. At
   each `compose a b` it walks `a` first to learn `offB := off + count a`,
   then either applies `Z_spiderFusion` (if `(offA, offB) = (idA, idB)`)
   or recurses into `b` and combines with `ZX.compose_congr`. For non-
   target subtrees the proof piece is `ZX.equiv_refl`.
3. `applyZxAlgFusion` combines the constructed proof with the residual
   via `ZX.equiv_trans` and leaves the user a `lhs' ≃ZX rhs` goal —
   usually closable with `rfl` if the user wrote `rhs` to match the
   raw fused form.

### When the tactic fails

- **Free `ZX` variables in `lhs`.** The walker hits the variable and
  has no constructor to discriminate on; `whnf` doesn't help. Restate
  the example with concrete sub-terms.
- **`×` notation gets parsed as `Prod`.** `ZX.compose`'s `×` and
  Lean's `Prod` `×` are both `infixl:55`, and in some elaboration
  contexts (multi-argument goal statements) the overload resolution
  emits spurious errors even though `ZX.compose` succeeds. Workaround:
  use `ZX.compose` explicitly in the statement.

### Extending to other rules

The reusable pieces in `Congruence.lean` (`ZX.compose_congr`,
`ZX.stack_congr`, `ZX.compose_assoc`) plus `ZX.equiv_refl`/`equiv_trans`
in `Semantics.lean` are sufficient for any tactic that wants to descend
to a target subterm and apply a proved equivalence at the leaf. Pattern
for a new `zx_alg_<rule>` tactic:

1. Write the leaf theorem (`Z_spiderFusion`-style) with `≃ZX`
   conclusion.
2. Write a computable structural matcher in `Rewrite.lean` (or write
   the matching inline in MetaM — `buildFusionProof` does the latter).
3. Copy `buildFusionProof` and swap the leaf application for the new
   theorem.
4. Add an `elab_rules` block with whatever syntax fits the rule's
   inputs.

### Out of scope (yet)

- Goal-state visualization for `≃ZX` (`zx_alg_show`). Needs an `evalZX`
  parallel of `evalZXDiagram` plus arity extraction from the goal type.
- Multi-leg spider fusion (requires generalized `Z_spiderFusion`).
- Fusion through intervening `wire`/`hadamard` chains.
- X-spider variants (need real X semantics — currently `.sem = 0`).
