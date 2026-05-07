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
  `⟦a ⨾ b⟧ = ⟦b⟧ * ⟦a⟧` (matrices act right-to-left).
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

`ZX.toHtml` renders an algebraic term in the existing `ZXWidget` by first
lowering it to a `ZXDiagram` via `ZX.toZXDiagram`. The lowering threads a
private `Frag` (diagram + open `left`/`right` port-id lists) through the
constructors:

- `wire` → identity Z-spider (degree-2, phase 0). A small unmarked dot;
  removable later via `IdentityRemoval` if you want a cleaner picture.
- `hadamard` → one `.hadamard` node, used as both ports.
- `spider c n m φ` → one node, `left = replicate n id`, `right = replicate m id`
  (parallel edges to the same node — the widget already draws these as bezier
  arcs).
- `stack` → concatenate fragments with id-shifted edges/ports.
- `compose a b` → wire `a.right` to `b.left` with `zipWith` edges.

Boundary `.input`/`.output` nodes are added **only** at the top level by
`ZX.toZXDiagram`, so internal fragments stay arity-pure during recursion.
This is rendering-only — there is no proof that `toZXDiagram` preserves
semantics (would need a `ZXDiagram` denotation, which doesn't exist yet).

## Proof tactics that worked here

- For `Fin.sum_univ_two` over `Fin (2^1)`: use `show (∑ s : Fin 2, …)` to coerce
  the index type — the lemma won't unify against `Fin (2^1)` directly even
  though they're defeq.
- Collapsing `(if h₁ then a else 0) * (if h₂ then b else 0)` to a single
  AND-indicator: `simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, ← ite_and]`.
  Note `simp` happens to apply `mul_ite` first, which controls which condition
  ends up "outside" in the resulting AND.
