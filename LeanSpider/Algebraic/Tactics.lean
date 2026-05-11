import LeanSpider.Algebraic.SpiderFusion
import LeanSpider.Algebraic.Congruence
import LeanSpider.Algebraic.Rewrite

open Lean Elab Tactic Meta

namespace LeanSpider.Algebraic

/-- Parse a goal of the form `lhs ≃ZX rhs` into its sides.
    `ZX.equiv` has signature `{n m} → ZX n m → ZX n m → Prop` so the
    elaborated expression is `@ZX.equiv n m lhs rhs` — 4 args. -/
def parseAlgEquivGoal (goalType : Expr) : TacticM (Expr × Expr) := do
  let goalType ← instantiateMVars goalType
  let (fn, args) := (goalType.getAppFn, goalType.getAppArgs)
  if fn.constName? == some ``ZX.equiv && args.size == 4 then
    return (args[2]!, args[3]!)
  throwError "Goal is not of the form `lhs ≃ZX rhs` (got: {goalType})"

/-- Walk a `ZX n m` expression in the same DFS order as `buildFrag` in
    `Visualize.lean`, building both the rewritten term and a proof
    `original ≃ZX rewritten`. At the target `compose` (whose children
    have node IDs `idA` and `idB`), applies `Z_spiderFusion`.

    Returns `(rewritten, proof, endOffset)`. -/
partial def buildFusionProof (z : Expr) (idA idB : Nat) (off : Nat) :
    MetaM (Expr × Expr × Nat) := do
  let z ← whnf z
  let f := z.getAppFn
  let name := f.constName?
  match name with
  | some ``ZX.empty =>
      let proof ← mkAppM ``ZX.equiv_refl #[z]
      return (z, proof, off)
  | some ``ZX.wire =>
      let proof ← mkAppM ``ZX.equiv_refl #[z]
      return (z, proof, off + 1)
  | some ``ZX.hadamard =>
      let proof ← mkAppM ``ZX.equiv_refl #[z]
      return (z, proof, off + 1)
  | some ``ZX.spider =>
      let proof ← mkAppM ``ZX.equiv_refl #[z]
      return (z, proof, off + 1)
  | some ``ZX.stack =>
      -- @ZX.stack n m p q a b — args 4 and 5 are the children
      let args := z.getAppArgs
      let a := args[4]!
      let b := args[5]!
      let (a', proofA, off1) ← buildFusionProof a idA idB off
      let (b', proofB, off2) ← buildFusionProof b idA idB off1
      let stacked ← mkAppM ``ZX.stack #[a', b']
      let proof ← mkAppM ``ZX.stack_congr #[proofA, proofB]
      return (stacked, proof, off2)
  | some ``ZX.compose =>
      -- @ZX.compose n m k a b — args 3 and 4 are the children
      let args := z.getAppArgs
      let a := args[3]!
      let b := args[4]!
      let offA := off
      -- Walk a first to determine offB
      let (a', proofA, offB) ← buildFusionProof a idA idB offA
      if offA == idA && offB == idB then
        -- Target compose. Reach for Z_spiderFusion. Extract n, k, α, β
        -- from the spiders a and b directly. Both are leaves (nodeCount 1),
        -- so the end offset is just offB + 1.
        let aWhnf ← whnf a
        let bWhnf ← whnf b
        let aArgs := aWhnf.getAppArgs   -- @ZX.spider .Z n 1 α
        let bArgs := bWhnf.getAppArgs   -- @ZX.spider .Z 1 k β
        unless aWhnf.getAppFn.constName? == some ``ZX.spider
            && bWhnf.getAppFn.constName? == some ``ZX.spider
            && aArgs.size == 4 && bArgs.size == 4 do
          throwError "Nodes {idA} and {idB} are adjacent under a `compose`, \
                     but the pair is not a fuseable Z-spider junction."
        let n := aArgs[1]!
        let α := aArgs[3]!
        let k := bArgs[2]!
        let β := bArgs[3]!
        let proof ← mkAppM ``Z_spiderFusion #[n, k, α, β]
        -- Construct the fused result: ZX.spider .Z n k (α + β)
        let sumPhase ← mkAppM ``HAdd.hAdd #[α, β]
        let colorZ := mkConst ``SpiderColor.Z
        let fused ← mkAppM ``ZX.spider #[colorZ, n, k, sumPhase]
        return (fused, proof, offB + 1)
      else
        let (b', proofB, offEnd) ← buildFusionProof b idA idB offB
        let composed ← mkAppM ``ZX.compose #[a', b']
        let proof ← mkAppM ``ZX.compose_congr #[proofA, proofB]
        return (composed, proof, offEnd)
  | _ => throwError "Unrecognized ZX expression head: {name}"

/-- The main tactic engine — mirrors `applyRewrite` in
    `LeanSpider/Tactics.lean` but for `≃ZX`. -/
def applyZxAlgFusion (idA idB : Nat) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let (lhs, rhs) ← parseAlgEquivGoal goalType
  -- Build the rewrite proof
  let (lhs', proof, _) ← buildFusionProof lhs idA idB 0
  -- New residual goal: lhs' ≃ZX rhs
  let newGoalType ← mkAppM ``ZX.equiv #[lhs', rhs]
  let newGoal ← mkFreshExprMVar newGoalType
  -- Combined proof: equiv_trans (lhs ≃ZX lhs') (lhs' ≃ZX rhs)
  let trans ← mkAppM ``ZX.equiv_trans #[proof, newGoal]
  goal.assign trans
  setGoals [newGoal.mvarId!]

elab "zx_alg_fusion " idA:num idB:num : tactic =>
  applyZxAlgFusion idA.getNat idB.getNat

end LeanSpider.Algebraic
