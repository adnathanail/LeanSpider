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

/-- The `AlgPhase` type as an `Expr` — used as the type filter when
    substituting symbolic phase free variables, and to type the placeholder
    `(0 : AlgPhase)` returned by `algPhaseZeroExpr`. -/
private def algPhaseTypeExpr : Expr := mkConst ``AlgPhase

/-- Build the placeholder phase `Expr`: `(0 : AlgPhase)`. Used to close
    a parameterized term before `Meta.evalExpr` so the eval can succeed —
    the visualized symbolic phases are recovered separately via the labels
    side-channel. -/
private def algPhaseZeroExpr : MetaM Expr :=
  mkAppOptM ``OfNat.ofNat #[some algPhaseTypeExpr, some (mkRawNatLit 0), none]

/-- Try to evaluate an `Expr` of type `AlgPhase` (a `ℚ`) to a concrete value.
    Returns `none` for symbolic phases (free variables, unreduced binders). -/
private unsafe def tryEvalAlgPhaseImpl (e : Expr) : MetaM (Option AlgPhase) := do
  try
    let v ← Meta.evalExpr AlgPhase algPhaseTypeExpr e
    return some v
  catch _ => return none

@[implemented_by tryEvalAlgPhaseImpl]
private opaque tryEvalAlgPhase (e : Expr) : MetaM (Option AlgPhase)

/-- Format an `AlgPhase` (a `ℚ`) using the same string convention as graph-side
    `Phase.format`. Routes through `AlgPhase.toGraphPhase` so display stays
    consistent across both representations. -/
private def algPhaseFormat (q : AlgPhase) : String :=
  q.toGraphPhase.format

/-- Render an `AlgPhase`-typed `Expr` as a display string. The walker
    prioritises *evaluation* over surface preservation: any sub-expression
    free of fvars is evaluated to a concrete `ℚ` and formatted via
    `algPhaseFormat`, so e.g. `phaseLit 1 4 + phaseLit 1 4` shows as `π/2`
    rather than `π/4 + π/4`. Surface `HAdd` / `HSub` / `Neg` combinators
    are only walked recursively when an fvar prevents evaluation. Free
    variables render as their user name; anything else falls back to
    `ppExpr`. -/
partial def phaseExprToLabel (e : Expr) : MetaM String := do
  let e ← instantiateMVars e
  let fallback : MetaM String := do
    return (← Lean.PrettyPrinter.ppExpr e).pretty
  -- 1. Free variable — render as the user name.
  if e.isFVar then
    let decl ← e.fvarId!.getDecl
    return decl.userName.toString
  -- 2. Closed (no fvars) — evaluate as ℚ and format. Reduces
  --    `phaseLit 1 4 + phaseLit 1 4` to `π/2`.
  if !e.hasFVar then
    match (← tryEvalAlgPhase e) with
    | some q => return algPhaseFormat q
    | none   => return ← fallback
  -- 3. Has fvars — recurse through surface combinators so closed
  --    sub-expressions still evaluate cleanly while symbolic parts
  --    preserve their user names.
  let (fn, args) := (e.getAppFn, e.getAppArgs)
  match fn.constName?, args.size with
  | some ``HAdd.hAdd, 6 =>
      return s!"{← phaseExprToLabel args[4]!} + {← phaseExprToLabel args[5]!}"
  | some ``HSub.hSub, 6 =>
      return s!"{← phaseExprToLabel args[4]!} - {← phaseExprToLabel args[5]!}"
  | some ``Neg.neg, 3 =>
      return s!"-{← phaseExprToLabel args[2]!}"
  | _, _ => fallback

/-- Walk a `ZX n m` `Expr` in the same DFS / offset scheme as `buildFrag`
    in `Visualize.lean` (and `buildFusionProof` below). At each spider
    whose phase contains a free variable, format the phase Expr via
    `phaseExprToLabel` and record `(nodeId, prettyString)`. Returns
    `(labels, endOffset)`. -/
partial def collectPhaseLabels (z : Expr) (off : Nat := 0) :
    MetaM (List (Nat × String) × Nat) := do
  let z ← whnf z
  let f := z.getAppFn
  match f.constName? with
  | some ``ZX.empty    => return ([], off)
  | some ``ZX.wire     => return ([], off + 1)
  | some ``ZX.hadamard => return ([], off + 1)
  | some ``ZX.spider   =>
      let args := z.getAppArgs
      if args.size = 4 then
        let phaseE := args[3]!
        if phaseE.hasFVar then
          let s ← phaseExprToLabel phaseE
          return ([(off, s)], off + 1)
      return ([], off + 1)
  | some ``ZX.stack    =>
      let args := z.getAppArgs
      let (la, off1) ← collectPhaseLabels args[4]! off
      let (lb, off2) ← collectPhaseLabels args[5]! off1
      return (la ++ lb, off2)
  | some ``ZX.compose  =>
      let args := z.getAppArgs
      let (la, off1) ← collectPhaseLabels args[3]! off
      let (lb, off2) ← collectPhaseLabels args[4]! off1
      return (la ++ lb, off2)
  | _ => return ([], off)

/-- Substitute every free variable of type `AlgPhase` in `z` with the
    placeholder `(0 : AlgPhase)`. After this the Expr is closed wrt
    `AlgPhase` fvars and can be fed to `Meta.evalExpr` — symbolic phases
    are recovered visually via the labels list emitted by
    `collectPhaseLabels`. -/
def substitutePhaseFVars (z : Expr) : MetaM Expr := do
  let lctx ← getLCtx
  let mut fvars : Array Expr := #[]
  for decl in lctx do
    unless decl.isImplementationDetail do
      if ← isDefEq decl.type algPhaseTypeExpr then
        fvars := fvars.push decl.toExpr
  if fvars.isEmpty then return z
  let placeholder ← algPhaseZeroExpr
  let replacements := fvars.map fun _ => placeholder
  return z.replaceFVars fvars replacements

/-- Build an `Expr` calling `ZX.toHtml`/`ZX.toHtmlPair` (with symbolic-phase
    labels) and evaluate it to `Html`. `ZX n m` is arity-indexed so we can't
    `Meta.evalExpr` the term itself — but `Html` is a plain type, so we
    evaluate the *application*. -/
private unsafe def evalAlgHtmlImpl (lhs : Expr) (rhs? : Option Expr) : MetaM Html := do
  let ty ← inferType lhs
  let some (nE, mE) := matchZXType? ty
    | throwError "evalAlgHtml: expected `ZX n m`, got {ty}"
  let (lhsLabels, _) ← collectPhaseLabels lhs
  let lhs' ← substitutePhaseFVars lhs
  let lhsLabelsE : Expr := Lean.toExpr lhsLabels
  let htmlE ← match rhs? with
    | none =>
        mkAppOptM ``ZX.toHtml
          #[some nE, some mE, some lhs', some lhsLabelsE]
    | some rhs =>
        let (rhsLabels, _) ← collectPhaseLabels rhs
        let rhs' ← substitutePhaseFVars rhs
        let rhsLabelsE : Expr := Lean.toExpr rhsLabels
        mkAppOptM ``ZX.toHtmlPair
          #[some nE, some mE, some lhs', some rhs',
            some lhsLabelsE, some rhsLabelsE]
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

/-- Walk a `ZX n m` expression in the same DFS order as `buildFrag` in
    `Visualize.lean`, building both the rewritten term and a proof
    `original ≃ZX rewritten`. At the target `compose` (whose children
    have node IDs `idA` and `idB`), applies `Z_spiderFusion` with the raw
    summed phase `α + β` — no fast-path simplification, since `AlgPhase = ℚ`
    handles phase arithmetic via `abel`/`ring`/`norm_num` at the user's
    discretion.

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
