import ZxLean.Axioms
import ZxLean.Visualize
import ProofWidgets.Component.HtmlDisplay

open Lean Elab Tactic Meta ProofWidgets

namespace ZxLean

-- == Evaluation (for visualization only) ==

private unsafe def evalZXDiagramImpl (e : Expr) : MetaM ZXDiagram :=
  Meta.evalExpr ZXDiagram (mkConst ``ZXDiagram) e

@[implemented_by evalZXDiagramImpl]
private opaque evalZXDiagram : Expr → MetaM ZXDiagram

-- == Goal parsing ==

/-- Extract LHS and RHS from a goal of the form `d ≈z d'` -/
private def parseEquivGoal (goalType : Expr) : TacticM (Expr × Expr) := do
  let some (lhs, rhs) := goalType.app2? ``ZXDiagram.equiv
    | throwError "Goal is not of the form `d ≈z d'`"
  return (lhs, rhs)

-- == Visualization ==

/-- Show a ZXDiagram in the InfoView -/
private def showDiagram (stx : Syntax) (label : String) (e : Expr) : TacticM Unit := do
  let d ← evalZXDiagram e
  let html := d.toHtml
  let msg ← MessageData.ofHtml html label
  logInfoAt stx msg

-- == Core rewrite tactic ==

/-- Apply a rewrite rule and show the result.
    Evaluates the rewrite via whnf (works because ZXDiagram uses List). -/
private def applyRewrite (stx : Syntax) (label : String)
    (rewriteFn soundAxiom : Name) (args : Array Expr) : TacticM Unit :=
    withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let (lhs, rhs) ← parseEquivGoal goalType

  -- Build the rewrite application and reduce via whnf
  let rewriteApp ← mkAppM rewriteFn (#[lhs] ++ args)
  let rewriteReduced ← whnf rewriteApp

  -- Check it returned `some d₁`
  let some (_, d₁) := rewriteReduced.app2? ``Option.some
    | throwError "{label} failed"

  -- New goal: d₁ ≈z rhs
  let newGoalType ← mkAppM ``ZXDiagram.equiv #[d₁, rhs]
  let newGoal ← mkFreshExprMVar newGoalType

  -- Build proof: equiv_trans (soundAxiom lhs args... d₁ rfl) newGoal
  let soundProof ← mkAppM soundAxiom (#[lhs] ++ args ++ #[d₁, ← mkEqRefl rewriteReduced])
  let transProof ← mkAppM ``ZXDiagram.equiv_trans #[soundProof, newGoal]
  goal.assign transProof

  -- Set remaining goal and show diagram
  setGoals [newGoal.mvarId!]
  showDiagram stx label d₁

-- == User-facing tactics ==

/-- Fuse two connected spiders of the same color. Shows the resulting diagram. -/
syntax "zx_spider_fusion" num num : tactic

elab_rules : tactic
  | `(tactic| zx_spider_fusion $a $b) =>
    applyRewrite a "Spider fusion"
      ``ZXDiagram.spiderFusion ``ZXDiagram.spiderFusion_sound
      #[mkNatLit a.getNat, mkNatLit b.getNat]

/-- Remove an identity (phase-0, degree-2) spider. Shows the resulting diagram. -/
syntax "zx_id_removal" num : tactic

elab_rules : tactic
  | `(tactic| zx_id_removal $a) =>
    applyRewrite a "Identity removal"
      ``ZXDiagram.identityRemoval ``ZXDiagram.identityRemoval_sound
      #[mkNatLit a.getNat]

/-- Show the current LHS diagram in the InfoView without modifying the goal. -/
elab tk:"zx_show" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let (lhs, _) ← parseEquivGoal goalType
  showDiagram tk "Current diagram" lhs

/-- Close a `d ≈z d` goal by reflexivity. -/
elab "zx_rfl" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let (lhs, _) ← parseEquivGoal goalType
  let reflProof ← mkAppM ``ZXDiagram.equiv_refl #[lhs]
  goal.assign reflProof

end ZxLean
