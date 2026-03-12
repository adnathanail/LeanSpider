import LeanZX.Axioms
import LeanZX.Visualize
import ProofWidgets.Component.HtmlDisplay

open Lean Elab Tactic Meta ProofWidgets

namespace LeanZX

-- == Evaluation (for visualization only) ==

private unsafe def evalZXDiagramImpl (e : Expr) : MetaM ZXDiagram :=
  Meta.evalExpr ZXDiagram (mkConst ``ZXDiagram) e

@[implemented_by evalZXDiagramImpl]
opaque evalZXDiagram : Expr → MetaM ZXDiagram

private unsafe def evalStringImpl (e : Expr) : MetaM String :=
  Meta.evalExpr String (mkConst ``String) e

@[implemented_by evalStringImpl]
opaque evalString : Expr → MetaM String

-- == Goal parsing ==

/-- Extract LHS and RHS from a goal of the form `d ≈z d'` -/
def parseEquivGoal (goalType : Expr) : TacticM (Expr × Expr) := do
  let goalType ← instantiateMVars goalType
  let some (lhs, rhs) := goalType.app2? ``ZXDiagram.equiv
    | throwError "Goal is not of the form `d ≈z d'`"
  return (lhs, rhs)

-- == Visualization ==

/-- Show a ZXDiagram in the InfoView -/
def showDiagram (stx : Syntax) (label : String) (e : Expr) : TacticM Unit := do
  let d ← evalZXDiagram e
  let html := d.toHtml
  let msg ← MessageData.ofHtml html label
  logInfoAt stx msg

-- == Core rewrite tactic ==

/-- Apply a rewrite rule and show the result.
    Evaluates the rewrite via whnf (works because ZXDiagram uses List). -/
def applyRewrite (stx : Syntax) (label : String)
    (rewriteFn soundAxiom : Name) (args : Array Expr) : TacticM Unit :=
    withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let (lhs, rhs) ← parseEquivGoal goalType

  -- Build the rewrite application and reduce via whnf
  let rewriteApp ← mkAppM rewriteFn (#[lhs] ++ args)
  let rewriteReduced ← whnf rewriteApp

  -- Check it returned `.ok d₁`
  let some (_, _, d₁) := rewriteReduced.app3? ``Except.ok
    | do
      -- Try to extract the error message from `.error msg`
      let some (_, _, msgExpr) := rewriteReduced.app3? ``Except.error | throwError "{label} failed"
      let msg ← try
                   let msgReduced ← whnf msgExpr
                   liftM (evalString msgReduced : MetaM String)
                 catch _ => pure s!"{label} failed"
      throwError "{msg}"

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

-- == General tactics ==

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
  let (lhs, rhs) ← parseEquivGoal goalType
  -- If the RHS is a metavar (e.g. from zx_explore), unify it with the LHS
  if rhs.isMVar then
    rhs.mvarId!.assign lhs
  let reflProof ← mkAppM ``ZXDiagram.equiv_refl #[lhs]
  goal.assign reflProof

/-- Start aimless exploration: introduces `∃ d', diagram ≈z d'` into `diagram ≈z ?d'`,
    then shows the diagram. Apply rewrites freely and close with `zx_rfl`. -/
elab tk:"zx_explore" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  -- Expect ∃ d', lhs ≈z d'
  let some (_, _) := goalType.app2? ``Exists
    | throwError "Expected goal of the form `∃ d', diagram ≈z d'`"
  -- Introduce the existential with a placeholder witness, reducing to `diagram ≈z ?_`
  evalTactic (← `(tactic| refine Exists.intro ?_ ?_))
  let goals ← getGoals
  -- Goals are [witness : ZXDiagram, proof : lhs ≈z ?_]. Focus on the proof goal.
  setGoals [goals[1]!]
  let goalType ← (← getMainGoal).getType
  let (lhs, _) ← parseEquivGoal goalType
  showDiagram tk "Current diagram" lhs

end LeanZX
