import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Combinators
import SpLean.Algebraic.Cast

/-!
# Yanking and bending

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

The fix is to write the arity down in the shape the layer being elaborated
wants to split it. For a numeral that means a numeral — `(wire ⊗ cap : ZX 3 1)`
leaves no `+` for the split to match against, so unification falls back to
reducing. For a variable arity there is always a `+`, so the ascription has to
put it in the right place: `bend_input`'s second layer splits its boundary
`(n + 1) | 1`, so it is ascribed `ZX (n + 1 + 1) _` and not the equally true
`ZX (n + 2) _`, which would be split `n | 2` and fail.

This is the same asymmetry that runs through `Combinators.lean` and
`Rules/Structural.lean` — `Nat.add` reducing only on its second argument —
showing up during elaboration rather than in a statement, and it bites whenever
a `≫`'s two layers split their shared boundary in different places. Note that
it is *only* an elaboration problem: unlike the gaps `ZX.cast` fills, both
sides here already have the same type, and no cast is involved or needed. The X-coloured cup and cap satisfy the same two
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

/-! ### Bending a spider's leg

A ZX diagram depends only on its graph, so a spider does not care which of its
legs are inputs and which are outputs — `Z 1 2` with its last output bent round
is `Z 2 1`. That is not something the other rules can say: every rule so far
preserves each spider's arity, and `≫` is directed, so nothing yet lets a leg
change sides.

This is the rule `cnot_cnot_rewrite` (`SemanticsTesting/09Rules.lean`) turns
on. The two CNOT forms are the same Z spider joined to the same X spider,
differing only in which way the joining wire is composed, i.e. in whether that
leg is an output of the Z and an input of the X or the other way round.

The two `_above` rules bend the *first* leg, over the top of the spider; the
two below them bend the *last* leg, under the bottom — which in a stack is the
next qubit down. Between them that is every leg a planar diagram can move:
bending an interior leg would route the wire past its neighbours, and that is a
crossing — see `Rules/Bialgebra.lean`. Only the `_above` pair needs `ZX.cast`,
because `1 + (1 + n)` and `2 + n` are not definitionally equal where
`(m + 1) + 1` and `m + 2` are. The cap and cup are Z ones, but either colour would do:
`X 2 0` and `Z 2 0` are proportional, and `≈zx` does not see the difference. -/

/-- Bend a spider's last output round to become its last input. -/
theorem bend_output (c : AlgSpColor) (n m : ℕ) (α : AlgPhase) :
    ((ZX.spider c n (m + 1) α ⊗ ZX.wire) ≫ (ZX.nWire m ⊗ ZX.cap : ZX (m + 2) m))
      ≈zx ZX.spider c (n + 1) m α := by
  sorry

/-- Bend a spider's *first* output round to become its first input, above the
spider rather than below it. -/
theorem bend_output_above (c : AlgSpColor) (n m : ℕ) (α : AlgPhase) :
    ZX.cast rfl (Nat.zero_add m)
        ((ZX.wire ⊗ ZX.spider c n (1 + m) α)
          ≫ ZX.cast (by omega : 2 + m = 1 + (1 + m)) rfl (ZX.cap ⊗ ZX.nWire m))
      ≈zx ZX.spider c (1 + n) m α := by
  sorry

/-- Bend a spider's *first* input round to become its first output, above the
spider rather than below it. -/
theorem bend_input_above (c : AlgSpColor) (n m : ℕ) (α : AlgPhase) :
    ZX.cast (Nat.zero_add n) rfl
        ((ZX.cup ⊗ ZX.nWire n : ZX (0 + n) (2 + n))
          ≫ ZX.cast (by omega : 1 + (1 + n) = 2 + n) rfl
              (ZX.wire ⊗ ZX.spider c (1 + n) m α))
      ≈zx ZX.spider c n (1 + m) α := by
  sorry

/-- Bend a spider's last input round to become its last output. -/
theorem bend_input (c : AlgSpColor) (n m : ℕ) (α : AlgPhase) :
    ((ZX.nWire n ⊗ ZX.cup : ZX n (n + 2))
        ≫ (ZX.spider c (n + 1) m α ⊗ ZX.wire : ZX (n + 1 + 1) (m + 1)))
      ≈zx ZX.spider c n (m + 1) α := by
  sorry

end SpLean.Algebraic
