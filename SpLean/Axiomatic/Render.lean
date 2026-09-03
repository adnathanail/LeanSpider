import SpLean.Axiomatic.Visualize
import SpLean.Axiomatic.Tactics
import ProofWidgets.Component.HtmlDisplay

/-! # Rendering graph-style `ZXDiagram`s

    The `MetaM` side of graph-style visualization: turning an `Expr` into
    `Html`. Kept apart from `Visualize.lean` (which is pure) so that
    `SpLean/Panel.lean` has one renderer per representation to dispatch
    between, mirroring `SpLean/Algebraic/Render.lean`.

    Both entry points here *evaluate* the term — `evalZXDiagram`, i.e.
    `Meta.evalExpr` — so they need it closed. That is the opposite of the
    algebraic side, which walks the `Expr` and can draw an open term. A
    `none` means "not this kind of expression at all"; a term of the right
    shape that cannot be evaluated throws, and the caller decides whether
    that is an error or simply nothing to draw. -/

open Lean Elab Meta ProofWidgets

namespace SpLean

/-- Render a goal `d₁ ≈z d₂` as the current diagram with the goal diagram
    alongside. `none` if `e` is not a ZX equivalence; throws if a side cannot
    be evaluated to a concrete diagram (it has free variables, say). -/
def zxEquivHtml? (e : Expr) : MetaM (Option Html) := do
  -- `consumeMData` because a goal type is not always the bare application it
  -- prints as: `have` (and anything else that hands the elaborator an expected
  -- type) wraps it in a `noImplicitLambda` annotation, and `app2?`/`getAppFn`
  -- do not see through `mdata`. Without this a panel goes blank the moment a
  -- proof introduces a hypothesis.
  let e := (← instantiateMVars e).consumeMData
  let some (lhs, rhs) := e.app2? ``ZXDiagram.equiv | return none
  let dLhs ← evalZXDiagram lhs
  -- An unassigned RHS (e.g. from `zx_explore`) means there is no goal to show yet.
  let goal? ← if rhs.hasExprMVar then pure none else some <$> evalZXDiagram rhs
  return some (dLhs.toHtml goal?)

/-- Render a bare `ZXDiagram`-valued term, e.g. a subterm selected with
    shift-click. `none` if `e` is not a `ZXDiagram` at all; throws if it is one
    that cannot be evaluated. -/
def zxDiagramHtml? (e : Expr) : MetaM (Option Html) := do
  let e := (← instantiateMVars e).consumeMData
  if !(← inferType e).isConstOf ``ZXDiagram then return none
  return some (← evalZXDiagram e).toHtml

end SpLean
