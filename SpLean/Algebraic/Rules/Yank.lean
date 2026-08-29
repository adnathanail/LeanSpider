import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Combinators

/-!
# Yanking (the snake equations)

A wire that goes up into a cup and back down through a cap pulls straight. This
is the rule that lets a wire be *bent*, and so the rule that relates two
diagrams which are the same graph composed in different directions — the gap
`cnot_cnot_equiv` (`SemanticsTesting/09Rules.lean`) runs into, where one
decomposition composes Z-then-X and the other X-then-Z.

Unlike bialgebra (`Rules/Bialgebra.lean`) these need no crossing, and unlike
the `⊗` unit and associativity laws they need no arity cast: the snake is
`ZX 1 3 ≫ ZX 3 1`, and every index in it is a numeral. So the yanking rules
are statable here even though the compact-closed *structure* they belong to is
not fully expressible — `ZX` can bend a wire but cannot cross two.

`ZX.cup`/`ZX.cap` are the phase-free Z spiders `Z 0 2` and `Z 2 0`, and
`ZX.cupX`/`ZX.capX` their X versions (`Combinators.lean`).

## Why the `: ZX 3 1` ascriptions

Without them these statements do not elaborate, with an arity error pointing at
a `wire`. The left layer of the snake has type `ZX 1 (2 + 1)` — the middle
arity arrives *unreduced*, in the shape the left layer built it — so the right
layer is elaborated against an expected `ZX (2 + 1) _` while its own `⊗` splits
that boundary as `1 + 2`. The two `+` applications unify argument by argument
before anything is reduced, `?n := 2` is committed to, and `ZX.wire` is then
asked to be a `ZX 2 _`.

Ascribing the middle arity as a numeral removes the `+` for the split to match
against, and unification falls back to reducing. This is the same asymmetry
that runs through `Combinators.lean` and `Rules/Structural.lean` — `Nat.add`
reducing only on its second argument — showing up during elaboration rather
than in a statement, and it bites whenever a `≫`'s two layers split their
shared boundary in different places. The X-coloured cup and cap satisfy the same two
equations, and for the same reason: `zSpiderSem` at arity `(2,0)` is
`if f 0 = f 1 then 1 else 0`, which is the contraction, and the X versions are
that conjugated by Hadamards.
-/

namespace SpLean.Algebraic

/-- The left snake pulls straight. -/
theorem yank_left :
    ((ZX.cup ⊗ ZX.wire) ≫ (ZX.wire ⊗ ZX.cap : ZX 3 1)) ≈zx ZX.wire := by
  sorry

/-- The right snake pulls straight. -/
theorem yank_right :
    ((ZX.wire ⊗ ZX.cup) ≫ (ZX.cap ⊗ ZX.wire : ZX 3 1)) ≈zx ZX.wire := by
  sorry

/-- The left snake, in X. -/
theorem yank_left_X :
    ((ZX.cupX ⊗ ZX.wire) ≫ (ZX.wire ⊗ ZX.capX : ZX 3 1)) ≈zx ZX.wire := by
  sorry

/-- The right snake, in X. -/
theorem yank_right_X :
    ((ZX.wire ⊗ ZX.cupX) ≫ (ZX.capX ⊗ ZX.wire : ZX 3 1)) ≈zx ZX.wire := by
  sorry

end SpLean.Algebraic
