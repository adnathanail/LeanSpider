import LSpec
import LeanSpider.Algebraic.Tactics

/-! Unit tests for `LeanSpider.Algebraic.phaseExprToLabel` — the MetaM
    walker that converts a `Phase`-typed `Expr` into its display string.
    Tests run at compile time via `#guard_msgs in #eval`; any divergence
    from the expected output fails the `lake build Tests` run.

    Covers: concrete literals (gcd + mod-2π normalization via
    `Phase.simplify`), surface `HAdd` / `Phase.add` combinators, free
    variables, and mixed symbolic-plus-concrete expressions.

    These tests don't go through the LSpec runner because
    `phaseExprToLabel` is `MetaM`-bound and `LSpec.test` only accepts
    pure `Prop`s. They still gate the build, which is enough for CI. -/

open Lean Elab Meta LeanSpider.Algebraic

namespace LeanSpider.Tests.PhaseLabel

/-- Build a `Phase.mk n d` `Expr` (used as a literal building block). -/
private def phaseLit (n : Int) (d : Nat) : MetaM Expr := do
  let numE : Expr := Lean.toExpr n
  let denE ← mkAppOptM ``OfNat.ofNat
                #[some (mkConst ``PNat), some (Lean.toExpr d), none]
  mkAppM ``Phase.mk #[numE, denE]

-- == Concrete literals ==

/-- info: "π/2" -/
#guard_msgs in #eval show MetaM String from do
  phaseExprToLabel (← phaseLit 1 2)

/-- info: "0" -/
#guard_msgs in #eval show MetaM String from do
  phaseExprToLabel (← phaseLit 0 1)

/-- info: "π" -/
#guard_msgs in #eval show MetaM String from do
  phaseExprToLabel (← phaseLit 1 1)

/-- info: "2π/3" -/
#guard_msgs in #eval show MetaM String from do
  phaseExprToLabel (← phaseLit 2 3)

-- `Phase.simplify` gcd-reduces ⟨2, 4⟩ to ⟨1, 2⟩.
/-- info: "π/2" -/
#guard_msgs in #eval show MetaM String from do
  phaseExprToLabel (← phaseLit 2 4)

-- `Phase.simplify` mod-2π reduces ⟨5, 2⟩ → ⟨1, 2⟩ (since 5/2 ≡ 1/2 mod 2).
/-- info: "π/2" -/
#guard_msgs in #eval show MetaM String from do
  phaseExprToLabel (← phaseLit 5 2)

-- Euclidean mod in Lean: -1 % 8 = 7, so ⟨-1, 4⟩ formats as 7π/4
-- (the same angle on the circle, just expressed with non-negative
-- numerator). Documents the simplify-on-format behaviour.
/-- info: "7π/4" -/
#guard_msgs in #eval show MetaM String from do
  phaseExprToLabel (← phaseLit (-1) 4)

-- == Surface combinators on closed phases ==
--    Crucial: must NOT unfold to `Phase.mk (a*d + c*b) (b*d)` —
--    that was the bug from the previous iteration of this walker.

/-- info: "π/4 + π/4" -/
#guard_msgs in #eval show MetaM String from do
  let a ← phaseLit 1 4
  let b ← phaseLit 1 4
  phaseExprToLabel (← mkAppM ``HAdd.hAdd #[a, b])

-- Direct `Phase.add` (in case some caller bypasses the typeclass).
/-- info: "π/4 + π/4" -/
#guard_msgs in #eval show MetaM String from do
  let a ← phaseLit 1 4
  let b ← phaseLit 1 4
  phaseExprToLabel (← mkAppM ``Phase.add #[a, b])

-- == Symbolic free variables ==

/-- info: "α" -/
#guard_msgs in #eval show MetaM String from do
  withLocalDeclD `α (mkConst ``Phase) fun α =>
    phaseExprToLabel α

/-- info: "α + β" -/
#guard_msgs in #eval show MetaM String from do
  withLocalDeclD `α (mkConst ``Phase) fun α =>
    withLocalDeclD `β (mkConst ``Phase) fun β => do
      phaseExprToLabel (← mkAppM ``HAdd.hAdd #[α, β])

-- == Mixed: symbolic + concrete ==
--    The original bug case — these previously printed
--    `α + { num := 1, den := 2 }`.

/-- info: "α + π/2" -/
#guard_msgs in #eval show MetaM String from do
  withLocalDeclD `α (mkConst ``Phase) fun α => do
    phaseExprToLabel (← mkAppM ``HAdd.hAdd #[α, ← phaseLit 1 2])

/-- info: "π/2 + α" -/
#guard_msgs in #eval show MetaM String from do
  withLocalDeclD `α (mkConst ``Phase) fun α => do
    phaseExprToLabel (← mkAppM ``HAdd.hAdd #[← phaseLit 1 2, α])

-- Nested combinators recurse correctly.
/-- info: "α + β + π/2" -/
#guard_msgs in #eval show MetaM String from do
  withLocalDeclD `α (mkConst ``Phase) fun α =>
    withLocalDeclD `β (mkConst ``Phase) fun β => do
      let inner ← mkAppM ``HAdd.hAdd #[α, β]
      phaseExprToLabel (← mkAppM ``HAdd.hAdd #[inner, ← phaseLit 1 2])

-- A trivial `TestSeq` so that `Tests/All.lean`'s aggregate has a stable
-- entry for this file. The real assertions are the `#guard_msgs` blocks
-- above; this just confirms the module loaded successfully under LSpec.
open LSpec in
def phaseLabelTests : TestSeq :=
  test "phaseExprToLabel module loaded" True

end LeanSpider.Tests.PhaseLabel
