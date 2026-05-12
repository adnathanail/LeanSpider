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

/-- Build a `Phase` `Expr` from a concrete `Phase` value. Lives this high
    in the file so `substitutePhaseFVars` (below) can build a placeholder. -/
private def phaseToExpr (γ : Phase) : MetaM Expr := do
  let numE : Expr := Lean.toExpr γ.num
  let denValE : Expr := Lean.toExpr γ.den.val
  let denE ← mkAppOptM ``OfNat.ofNat #[some (mkConst ``PNat), some denValE, none]
  mkAppM ``Phase.mk #[numE, denE]

/-- Try to evaluate an `Expr` of type `Phase` to a concrete `Phase` value.
    Returns `none` for symbolic phases (free variables, unreduced binders). -/
private unsafe def tryEvalPhaseImpl (e : Expr) : MetaM (Option Phase) := do
  try
    let v ← Meta.evalExpr Phase (mkConst ``Phase) e
    return some v
  catch _ => return none

@[implemented_by tryEvalPhaseImpl]
private opaque tryEvalPhase (e : Expr) : MetaM (Option Phase)

/-- Render a `Phase`-typed `Expr` as a display string. Concrete sub-Exprs go
    through the Lean-side formatter `Phase.format` (e.g. `π/2`); free
    variables render as their user name; `+`/`-`/unary minus combinators
    recurse on their arguments. Falls back to `ppExpr` for shapes the
    walker doesn't recognise.

    Important: do **not** `whnf` the Expr before matching — `whnf` would
    unfold `HAdd.hAdd Phase Phase Phase _` into `Phase.add` and then into
    `Phase.mk (a.num * b.den + b.num * a.den) (a.den * b.den)`, exposing
    Phase's internal arithmetic to the label string. We need to recognise
    the surface form (`HAdd.hAdd …`) first. -/
partial def phaseExprToLabel (e : Expr) : MetaM String := do
  let e ← instantiateMVars e
  let fallback : MetaM String := do
    return (← Lean.PrettyPrinter.ppExpr e).pretty
  -- 1. Free variable — render as the user name.
  if e.isFVar then
    let decl ← e.fvarId!.getDecl
    return decl.userName.toString
  -- 2. Structural combinators — recurse without reducing.
  let (fn, args) := (e.getAppFn, e.getAppArgs)
  match fn.constName?, args.size with
  | some ``HAdd.hAdd, 6 =>
      return s!"{← phaseExprToLabel args[4]!} + {← phaseExprToLabel args[5]!}"
  | some ``HSub.hSub, 6 =>
      return s!"{← phaseExprToLabel args[4]!} - {← phaseExprToLabel args[5]!}"
  | some ``Phase.add, 2 =>
      return s!"{← phaseExprToLabel args[0]!} + {← phaseExprToLabel args[1]!}"
  | some ``Neg.neg, 3 =>
      return s!"-{← phaseExprToLabel args[2]!}"
  | _, _ =>
      -- 3. Closed Phase — evaluate and format. Otherwise fall back to ppExpr.
      if !e.hasFVar then
        match (← tryEvalPhase e) with
        | some p => return p.format
        | none   => fallback
      else fallback

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

/-- Substitute every free variable of type `Phase` in `z` with a placeholder
    `Phase.mk 0 1`. After this the Expr is closed wrt Phase fvars and can be
    fed to `Meta.evalExpr` — symbolic phases are recovered visually via the
    labels list emitted by `collectPhaseLabels`. -/
def substitutePhaseFVars (z : Expr) : MetaM Expr := do
  let phaseTy := mkConst ``Phase
  let lctx ← getLCtx
  let mut fvars : Array Expr := #[]
  for decl in lctx do
    unless decl.isImplementationDetail do
      if ← isDefEq decl.type phaseTy then
        fvars := fvars.push decl.toExpr
  if fvars.isEmpty then return z
  let placeholder ← phaseToExpr ⟨0, 1⟩
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

/-- Walk a `ZX n m` expression like `buildFusionProof`, but at the spider
    with node ID `id` rewrite its phase from `α + (-α)` to the default
    zero phase using `ZX.spider_add_neg_self`. The phase must syntactically
    match `HAdd.hAdd _ _ _ _ α (Neg.neg _ _ α)` — no semantic phase
    simplification is attempted, mirroring `zx_alg_fusion`'s surface match.

    Returns `(rewritten, proof, endOffset)`. -/
partial def buildPhaseCancelProof (z : Expr) (id : Nat) (off : Nat) :
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
      if off == id then
        let args := z.getAppArgs
        unless args.size == 4 do
          throwError "ZX.spider: expected 4 args, got {args.size}"
        let φ := args[3]!
        -- Match `HAdd.hAdd _ _ _ _ α (Neg.neg _ _ α)` on the surface form
        -- — do NOT whnf φ, that would expose Phase.add's internals.
        let phaseFn := φ.getAppFn
        let phaseArgs := φ.getAppArgs
        unless phaseFn.constName? == some ``HAdd.hAdd && phaseArgs.size == 6 do
          throwError "Node {id}'s phase is not of the form `α + (-α)` \
                     (head: {phaseFn})."
        let α := phaseArgs[4]!
        let negTerm := phaseArgs[5]!
        let negFn := negTerm.getAppFn
        let negArgs := negTerm.getAppArgs
        unless negFn.constName? == some ``Neg.neg && negArgs.size == 3 do
          throwError "Node {id}'s phase is `α + β` but β is not `-_`."
        let β := negArgs[2]!
        unless ← isDefEq α β do
          throwError "Node {id}'s phase is `α + (-β)` but α ≠ β."
        let c := args[0]!
        let nE := args[1]!
        let mE := args[2]!
        -- The lemma's RHS *is* the rewritten spider — pull it from the
        -- proof's type so default-arg / implicit handling stays consistent.
        let proof ← mkAppOptM ``ZX.spider_add_neg_self
          #[some c, some nE, some mE, some α]
        let proofTy ← inferType proof
        let proofArgs := proofTy.getAppArgs
        unless proofArgs.size == 4 do
          throwError "spider_add_neg_self: unexpected equiv arity \
                     ({proofArgs.size}, expected 4)"
        let replaced := proofArgs[3]!
        return (replaced, proof, off + 1)
      else
        let proof ← mkAppM ``ZX.equiv_refl #[z]
        return (z, proof, off + 1)
  | some ``ZX.stack =>
      let args := z.getAppArgs
      let a := args[4]!
      let b := args[5]!
      let (a', proofA, off1) ← buildPhaseCancelProof a id off
      let (b', proofB, off2) ← buildPhaseCancelProof b id off1
      let stacked ← mkAppM ``ZX.stack #[a', b']
      let proof ← mkAppM ``ZX.stack_congr #[proofA, proofB]
      return (stacked, proof, off2)
  | some ``ZX.compose =>
      let args := z.getAppArgs
      let a := args[3]!
      let b := args[4]!
      let (a', proofA, off1) ← buildPhaseCancelProof a id off
      let (b', proofB, off2) ← buildPhaseCancelProof b id off1
      let composed ← mkAppM ``ZX.compose #[a', b']
      let proof ← mkAppM ``ZX.compose_congr #[proofA, proofB]
      return (composed, proof, off2)
  | _ => throwError "Unrecognized ZX expression head: {name}"

/-- Engine for `zx_alg_phase_cancel`, mirroring `applyZxAlgFusion`. -/
def applyZxAlgPhaseCancel (id : Nat) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let (lhs, rhs) ← parseAlgEquivGoal goalType
  let (lhs', proof, _) ← buildPhaseCancelProof lhs id 0
  let newGoalType ← mkAppM ``ZX.equiv #[lhs', rhs]
  let newGoal ← mkFreshExprMVar newGoalType
  let trans ← mkAppM ``ZX.equiv_trans #[proof, newGoal]
  goal.assign trans
  setGoals [newGoal.mvarId!]

elab tk:"zx_alg_phase_cancel " id:num : tactic => do
  applyZxAlgPhaseCancel id.getNat
  withMainContext do
    let goalType ← (← getMainGoal).getType
    let (lhs', rhs) ← parseAlgEquivGoal goalType
    showAlgDiagram tk "After phase cancellation" lhs' (some rhs)

end LeanSpider.Algebraic
