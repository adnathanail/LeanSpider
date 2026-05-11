import LeanSpider.Algebraic.SpiderFusion
import LeanSpider.Algebraic.Congruence
import LeanSpider.Algebraic.Rewrite
import LeanSpider.Algebraic.Visualize
import ProofWidgets.Component.HtmlDisplay

open Lean Elab Tactic Meta ProofWidgets

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

-- == Visualization helpers ==

/-- If `ty` is `ZX n m`, return `(n, m)` as expressions. -/
private def matchZXType? (ty : Expr) : Option (Expr × Expr) :=
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  if fn.constName? == some ``ZX && args.size == 2 then
    some (args[0]!, args[1]!)
  else none

/-- Build an `Expr` calling `ZX.toHtml`/`ZX.toHtmlPair` and evaluate it to
    `Html`. `ZX n m` is arity-indexed so we can't `Meta.evalExpr` the term
    itself — but `Html` is a plain type, so we evaluate the *application*. -/
private unsafe def evalAlgHtmlImpl (lhs : Expr) (rhs? : Option Expr) : MetaM Html := do
  let ty ← inferType lhs
  let some (nE, mE) := matchZXType? ty
    | throwError "evalAlgHtml: expected `ZX n m`, got {ty}"
  let htmlE ← match rhs? with
    | none     => mkAppOptM ``ZX.toHtml     #[some nE, some mE, some lhs]
    | some rhs => mkAppOptM ``ZX.toHtmlPair #[some nE, some mE, some lhs, some rhs]
  Meta.evalExpr Html (mkConst ``ProofWidgets.Html) htmlE

@[implemented_by evalAlgHtmlImpl]
opaque evalAlgHtml (lhs : Expr) (rhs? : Option Expr) : MetaM Html

/-- Log a widget showing `lhs` on the `Current` panel and (when concrete)
    `rhs?` on the `Goal` panel. Render failures are downgraded to a warning
    so visualization never blocks an otherwise-successful proof. -/
def showAlgDiagram (stx : Syntax) (label : String)
    (lhs : Expr) (rhs? : Option Expr := none) : TacticM Unit := do
  let rhs? := rhs?.filter (fun r => !r.isMVar)
  try
    let html ← evalAlgHtml lhs rhs?
    let msg ← Lean.MessageData.ofHtml html label
    logInfoAt stx msg
  catch e =>
    logWarningAt stx m!"could not render ZX diagram: {e.toMessageData}"

/-- Combined spider fusion + phase simplification. The integer equation
    in `h` is decidable when `α`, `β`, `γ` are concrete `Phase` literals,
    so the tactic can supply it via `decide`. For symbolic phases, fall
    back to plain `Z_spiderFusion` instead. -/
private theorem Z_spiderFusion_simp (n k : Nat) (α β γ : Phase)
    (h : (α + β).num * ((γ.den : ℕ) : Int) = γ.num * (((α + β).den : ℕ) : Int)) :
    (ZX.spider .Z n 1 α × ZX.spider .Z 1 k β) ≃ZX ZX.spider .Z n k γ :=
  ZX.equiv_trans (Z_spiderFusion n k α β) (spider_phase_eq (congr_phase h))

/-- Reduce a `Phase` by dividing `num` and `den` by their gcd. Does NOT
    reduce numerator mod `2 * den` — that wouldn't preserve `congr_phase`'s
    integer equation (e.g. `⟨5,2⟩` vs `⟨1,2⟩` mod 2π satisfies
    `phaseToComplex` equality but not `5*2 = 1*2`). -/
private def gcdReducePhase (p : Phase) : Phase :=
  let dN : Nat := p.den
  let g : Nat := Nat.gcd p.num.natAbs dN
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ p.den.pos
  have hd : 0 < dN / g :=
    Nat.div_pos (Nat.le_of_dvd p.den.pos (Nat.gcd_dvd_right _ _)) hg
  { num := p.num / (g : Int), den := ⟨dN / g, hd⟩ }

/-- Try to evaluate an `Expr` of type `Phase` to a concrete `Phase` value.
    Returns `none` for symbolic phases (free variables, unreduced binders). -/
private unsafe def tryEvalPhaseImpl (e : Expr) : MetaM (Option Phase) := do
  try
    let v ← Meta.evalExpr Phase (mkConst ``Phase) e
    return some v
  catch _ => return none

@[implemented_by tryEvalPhaseImpl]
private opaque tryEvalPhase (e : Expr) : MetaM (Option Phase)

/-- Build a `Phase` `Expr` from a concrete `Phase` value. -/
private def phaseToExpr (γ : Phase) : MetaM Expr := do
  let numE : Expr := Lean.toExpr γ.num
  let denValE : Expr := Lean.toExpr γ.den.val
  let denE ← mkAppOptM ``OfNat.ofNat #[some (mkConst ``PNat), some denValE, none]
  mkAppM ``Phase.mk #[numE, denE]

/-- Walk a `ZX n m` expression in the same DFS order as `buildFrag` in
    `Visualize.lean`, building both the rewritten term and a proof
    `original ≃ZX rewritten`. At the target `compose` (whose children
    have node IDs `idA` and `idB`), applies `Z_spiderFusion` — and, when
    both spider phases are concrete `Phase` literals, also gcd-reduces
    the summed phase via `Z_spiderFusion_simp`.

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
        let colorZ := mkConst ``SpiderColor.Z
        -- If both phases are concrete `Phase` literals, gcd-reduce the
        -- summed phase and discharge the integer congruence via `decide`.
        -- Otherwise fall back to raw `Z_spiderFusion` (symbolic phases).
        let αVal? ← tryEvalPhase α
        let βVal? ← tryEvalPhase β
        match αVal?, βVal? with
        | some αV, some βV =>
            let γV := gcdReducePhase (αV + βV)
            let γE ← phaseToExpr γV
            let simpPartial ← mkAppOptM ``Z_spiderFusion_simp
              #[some n, some k, some α, some β, some γE]
            let partialTy ← inferType simpPartial
            let hType ← match partialTy with
              | .forallE _ d _ _ => pure d
              | _ => throwError "Z_spiderFusion_simp: expected forall (got {partialTy})"
            let hProof ← mkDecideProof hType
            let proof := mkApp simpPartial hProof
            let fused ← mkAppM ``ZX.spider #[colorZ, n, k, γE]
            return (fused, proof, offB + 1)
        | _, _ =>
            let proof ← mkAppM ``Z_spiderFusion #[n, k, α, β]
            let sumPhase ← mkAppM ``HAdd.hAdd #[α, β]
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

elab tk:"zx_alg_fusion " idA:num idB:num : tactic => do
  applyZxAlgFusion idA.getNat idB.getNat
  withMainContext do
    let goalType ← (← getMainGoal).getType
    let (lhs', rhs) ← parseAlgEquivGoal goalType
    showAlgDiagram tk "After spider fusion" lhs' (some rhs)

end LeanSpider.Algebraic
