import SpLean.Algebraic.ToHypergraph
import SpLean.Hypergraph.Search

/-!
# `zx_iso`: equivalence by hypergraph isomorphism, without writing the isomorphism

Closes a goal `x ≈zx y` for closed terms by lowering both to hypergraphs,
*searching* for an isomorphism, and emitting it as a certificate whose
conditions the kernel checks with `decide`.

The split is deliberate: the search (`SpLean.Hypergraph.Search.findTables`) is
untrusted and could be replaced wholesale without touching soundness, because
nothing it returns is believed — `Iso.ofTables` re-checks every condition. A
wrong answer costs a failed tactic, never a bad proof.

This is what the hand-written certificate in `SemanticsTesting/10Hypergraph.lean`
became: the tables there are exactly what the search now finds.
-/

open Lean Elab Tactic Meta SpLean.Hypergraph

namespace SpLean.Algebraic

/-- What decides whether two boxes may be matched: colour, and phase as a
rational. Only used to guide the search, so a key that conflates two labels
would cost a failed search, not an unsound proof — `Iso.ofTables` checks the
labels for real. -/
def algLabelKey (L : Label AlgPhase) : ℕ × Int × ℕ :=
  match L with
  | .spider .Z φ => (0, φ.toRat.num, φ.toRat.den)
  | .spider .X φ => (1, φ.toRat.num, φ.toRat.den)
  | .hadamard => (2, 0, 1)

private unsafe def hypDataOfExprImpl (e : Expr) : MetaM HypData := do
  let h ← mkAppM ``ZX.toHyp #[e]
  let d ← mkAppM ``Hyp.data #[mkConst ``algLabelKey, h]
  Meta.evalExpr HypData (mkConst ``HypData) d

/-- Lower a `ZX n m` `Expr` to its hypergraph and read it off as plain data.
The one `unsafe` step, sealed here as `Render.lean` seals its own. -/
@[implemented_by hypDataOfExprImpl]
private opaque hypDataOfExpr (e : Expr) : MetaM HypData

/-- Close `x ≈zx y` by finding a hypergraph isomorphism between the two sides. -/
elab "zx_iso" : tactic => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some (_, _, x, y) := ty.app4? ``ZX.Equiv
    | throwError "zx_iso: goal is not of the form `x ≈zx y`, but{indentExpr ty}"
  -- Both sides are *evaluated* to hypergraphs, so both have to be closed. A
  -- diagram with a variable phase in it has no hypergraph to compute, and
  -- without this check the failure surfaces as a kernel error about free
  -- variables rather than as anything a reader could act on.
  for e in [x, y] do
    if e.hasFVar || e.hasMVar then
      throwError "zx_iso: needs closed diagrams, but{indentExpr e}\nmentions a variable. A diagram parameterised by a phase has no hypergraph to compute; prove it by rewriting instead."
  let dx ← hypDataOfExpr x
  let dy ← hypDataOfExpr y
  let some t := Search.findTables dx dy
    | throwError "zx_iso: no isomorphism found between the hypergraphs of\
        {indentExpr x}\nand{indentExpr y}"
  let stx ← `(term|
    ZX.Equiv.of_hyp_iso
      (Iso.ofTables
        (w := fun a => List.getD $(quote t.w) a 0)
        (wInv := fun a => List.getD $(quote t.wInv) a 0)
        (bp := fun a => List.getD $(quote t.bp) a 0)
        (bpInv := fun a => List.getD $(quote t.bpInv) a 0)
        (lp := fun i k => List.getD (List.getD $(quote t.lp) i []) k 0)
        (lpInv := fun i k => List.getD (List.getD $(quote t.lpInv) i []) k 0)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        -- The labels carry phases, and a phase is a rational: `decide` cannot
        -- evaluate `ℚ` equality in the kernel (`Rat`'s operations go through
        -- `Nat.gcd`). Matched boxes have syntactically equal labels, though, so
        -- `rfl` settles each one without deciding anything.
        (by first | decide | (intro i; fin_cases i <;> rfl))
        (by decide)))
  -- The `decide`s evaluate the two hypergraphs, and on anything past a couple
  -- of spiders that goes deeper than the default recursion limit. Raise it
  -- here rather than making every call site do it.
  let e ← withOptions (fun o => o.set `maxRecDepth (100000 : Nat)) do
    elabTermEnsuringType stx ty
  goal.assign e

end SpLean.Algebraic
