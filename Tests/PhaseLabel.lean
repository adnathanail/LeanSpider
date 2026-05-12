import LSpec
import LeanSpider.Algebraic.Tactics

/-! Unit tests for `LeanSpider.Algebraic.phaseExprToLabel` — the MetaM
    walker that converts an `AlgPhase`-typed `Expr` into its display string.
    Tests run at compile time via `#guard_msgs in #eval`; any divergence
    from the expected output fails the `lake build Tests` run.

    Covers: concrete `phaseLit` literals (gcd + mod-2π normalization happens
    in the graph-side bridge `AlgPhase.toGraphPhase` + `Phase.simplify`),
    surface `HAdd` / `Neg` combinators, free variables, and mixed
    symbolic-plus-concrete expressions.

    These tests don't go through the LSpec runner because
    `phaseExprToLabel` is `MetaM`-bound and `LSpec.test` only accepts
    pure `Prop`s. They still gate the build, which is enough for CI. -/

open Lean Elab Meta LeanSpider.Algebraic

namespace LeanSpider.Tests.PhaseLabel

/-- Build a `LeanSpider.Algebraic.phaseLit p q` `Expr` of type `AlgPhase`. -/
private def phaseLit (p q : Int) : MetaM Expr := do
  mkAppM ``LeanSpider.Algebraic.phaseLit #[Lean.toExpr p, Lean.toExpr q]

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

-- ℚ auto-reduces 2/4 → 1/2; formatted as "π/2".
/-- info: "π/2" -/
#guard_msgs in #eval show MetaM String from do
  phaseExprToLabel (← phaseLit 2 4)

-- `Phase.simplify` (in the graph-side display bridge) mod-2π reduces 5/2 → 1/2.
/-- info: "π/2" -/
#guard_msgs in #eval show MetaM String from do
  phaseExprToLabel (← phaseLit 5 2)

-- Lean's Euclidean mod gives -1 % 8 = 7, so the angle prints as 7π/4.
/-- info: "7π/4" -/
#guard_msgs in #eval show MetaM String from do
  phaseExprToLabel (← phaseLit (-1) 4)

-- == Surface combinators on closed phases ==
--    Closed sums get evaluated as `ℚ` and rendered as a single literal:
--    `phaseLit 1 4 + phaseLit 1 4` simplifies to `π/2`.

/-- info: "π/2" -/
#guard_msgs in #eval show MetaM String from do
  let a ← phaseLit 1 4
  let b ← phaseLit 1 4
  phaseExprToLabel (← mkAppM ``HAdd.hAdd #[a, b])

-- == Symbolic free variables ==

/-- info: "α" -/
#guard_msgs in #eval show MetaM String from do
  withLocalDeclD `α (mkConst ``AlgPhase) fun α =>
    phaseExprToLabel α

/-- info: "α + β" -/
#guard_msgs in #eval show MetaM String from do
  withLocalDeclD `α (mkConst ``AlgPhase) fun α =>
    withLocalDeclD `β (mkConst ``AlgPhase) fun β => do
      phaseExprToLabel (← mkAppM ``HAdd.hAdd #[α, β])

-- == Mixed: symbolic + concrete ==

/-- info: "α + π/2" -/
#guard_msgs in #eval show MetaM String from do
  withLocalDeclD `α (mkConst ``AlgPhase) fun α => do
    phaseExprToLabel (← mkAppM ``HAdd.hAdd #[α, ← phaseLit 1 2])

/-- info: "π/2 + α" -/
#guard_msgs in #eval show MetaM String from do
  withLocalDeclD `α (mkConst ``AlgPhase) fun α => do
    phaseExprToLabel (← mkAppM ``HAdd.hAdd #[← phaseLit 1 2, α])

-- Nested combinators recurse correctly.
/-- info: "α + β + π/2" -/
#guard_msgs in #eval show MetaM String from do
  withLocalDeclD `α (mkConst ``AlgPhase) fun α =>
    withLocalDeclD `β (mkConst ``AlgPhase) fun β => do
      let inner ← mkAppM ``HAdd.hAdd #[α, β]
      phaseExprToLabel (← mkAppM ``HAdd.hAdd #[inner, ← phaseLit 1 2])

-- Unary minus on a free variable.
/-- info: "-α" -/
#guard_msgs in #eval show MetaM String from do
  withLocalDeclD `α (mkConst ``AlgPhase) fun α => do
    phaseExprToLabel (← mkAppM ``Neg.neg #[α])

-- A trivial `TestSeq` so that `Tests/All.lean`'s aggregate has a stable
-- entry for this file. The real assertions are the `#guard_msgs` blocks
-- above; this just confirms the module loaded successfully under LSpec.
open LSpec in
def phaseLabelTests : TestSeq :=
  test "phaseExprToLabel module loaded" True

end LeanSpider.Tests.PhaseLabel
