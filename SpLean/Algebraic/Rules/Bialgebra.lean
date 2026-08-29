import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Combinators

/-!
# Bialgebra and strong complementarity — not statable yet

These two are the standard rules this module cannot state, and the obstruction
is the same for both: **`ZX` has no crossing**.

The bialgebra rule is

    X 2 1 ≫ Z 1 2  ≈zx  (Z 1 2 ⊗ Z 1 2) ≫ σ ≫ (X 2 1 ⊗ X 2 1)

where `σ : ZX 2 2` swaps its two wires — the right-hand side is the four-cycle
`K₂,₂`, and with its two inputs on the left and two outputs on the right it
cannot be drawn in the plane without one wire crossing another. Strong
complementarity (`Axiomatic/Rules/StrongComp.lean`) is the `n`-ary version of
the same rule, a complete bipartite graph between the two spiders' neighbours,
and needs arbitrary permutations rather than a single swap.

`ZX`'s generators are `empty`, `wire`, `hadamard`, `spider`, `stack` and
`compose`, which generate exactly the *planar* diagrams. A swap is not among
them and cannot be derived: cups and caps (`ZX.cup`/`ZX.cap` in
`Combinators.lean`) do not help, since in a compact closed category the
symmetry is what cups and caps are defined *against*, not the other way round.

So this file deliberately holds no `sorry`ed theorem — a stub whose statement
cannot be written is not a stub. Unblocking it is a change to the ADT, not to
`Rules/`:

- add a `swap : ZX 2 2` constructor (or a general `perm : (σ : Equiv.Perm (Fin n)) → ZX n n`,
  which is what strong complementarity needs and what the "permuting wires is
  reindexing a sum" note in `SpLean/Algebraic/CLAUDE.md` anticipates),
- give it a `ZX.sem` clause — for `swap`, `if f 0 = g 1 ∧ f 1 = g 0 then 1 else 0`;
  for `perm`, a reindexing of the boundary assignment,
- teach `Visualize.lean` to lay it out, and `Render.lean` to walk it.

`Rules/Hopf.lean` is the part of the disconnecting story that *is* statable:
its two connecting wires are parallel, so no crossing is needed.
-/

namespace SpLean.Algebraic

end SpLean.Algebraic
