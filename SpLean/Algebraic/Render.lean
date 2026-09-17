import SpLean.Algebraic.Visualize
import SpLean.Algebraic.Equiv
import ProofWidgets.Component.HtmlDisplay

/-! # Rendering algebraic `ZX n m` terms

    The `MetaM` side of algebraic visualization: turning a `ZX n m` `Expr`
    into `Html`. Kept apart from `Visualize.lean` (which is pure) so that
    the `#zx` command in `SpLean/Panel.lean` can draw algebraic terms.

    The term is walked at the `Expr` level rather than evaluated, because a
    `ZX n m` need not be closed: `abbrev f (α : AlgPhase) : ZX 0 0` is a
    perfectly good diagram whose phase is a *variable*. The walker binds any
    leading `∀`s, so `#zx f` draws the spider with `α` beside it, and only a
    phase it cannot evaluate is printed symbolically — a closed phase still
    goes through `AlgPhase.format`, exactly as a closed term's would. -/

open Lean Elab Meta ProofWidgets

namespace SpLean.Algebraic

/-- Is `ty` of the form `ZX n m`? -/
private def isZXType (ty : Expr) : Bool :=
  ty.getAppFn.constName? == some ``ZX && ty.getAppNumArgs == 2

private def spiderColorOfExpr (e : Expr) : MetaM AlgSpColor := do
  match (← whnf e).constName? with
  | some ``AlgSpColor.Z => return .Z
  | some ``AlgSpColor.X => return .X
  | _ => throwError "#zx: cannot tell a spider's colour from{indentExpr e}"

/-- A spider's arity has to be a concrete number for the layout to place its
    legs, so an arity that is still a variable is an error rather than a
    symbolic label. -/
private def arityOfExpr (e : Expr) : MetaM Nat := do
  let some n ← (evalNat e).run
    | throwError "#zx: a spider's arity must be a literal, got{indentExpr e}"
  return n

private unsafe def phaseTextOfExprImpl (e : Expr) : MetaM String := do
  if !e.hasFVar && !e.hasMVar then
    try
      return ← Meta.evalExpr String (mkConst ``String) (← mkAppM ``AlgPhase.format #[e])
    catch _ =>
      -- Not evaluable after all (e.g. an opaque constant); fall through to
      -- printing it, which is still a better diagram than no diagram.
      pure ()
  return toString (← ppExpr e)

/-- The text to draw for a phase argument. A closed phase is evaluated and
    formatted; anything mentioning a variable or metavariable is printed as it
    is written, so `α` and `β + π/4` reach the widget as themselves.

    `Meta.evalExpr` is why this is the one `unsafe` step of the walk, and why
    it is sealed behind an `opaque` here rather than at the top of it: the
    walker itself is ordinary `MetaM` code. -/
@[implemented_by phaseTextOfExprImpl]
private opaque phaseTextOfExpr (e : Expr) : MetaM String

/-- Walk a `ZX n m` `Expr` into a `ZXSkel`. `whnf` at each step unfolds the
    definitions between one constructor and the next, so an `abbrev` naming a
    subdiagram is transparent here. -/
private partial def zxSkelOfExpr (e : Expr) : MetaM ZXSkel := do
  let e ← whnf e
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``ZX.empty    => return .empty
  | some ``ZX.wire     => return .wire
  | some ``ZX.hadamard => return .hadamard
  | some ``ZX.swap     => return .swap
  | some ``ZX.spider =>
    -- `spider (c) (n m) (φ)` — four explicit arguments, no indices.
    unless args.size == 4 do throwError "#zx: malformed spider{indentExpr e}"
    let c ← spiderColorOfExpr args[0]!
    let n ← arityOfExpr args[1]!
    let m ← arityOfExpr args[2]!
    return .spider c n m (← phaseTextOfExpr args[3]!)
  | some ``ZX.stack =>
    -- `stack {n m p q} a b`
    unless args.size == 6 do throwError "#zx: malformed stack{indentExpr e}"
    return .stack (← zxSkelOfExpr args[4]!) (← zxSkelOfExpr args[5]!)
  | some ``ZX.compose =>
    -- `compose {n m k} a b`
    unless args.size == 5 do throwError "#zx: malformed compose{indentExpr e}"
    return .compose (← zxSkelOfExpr args[3]!) (← zxSkelOfExpr args[4]!)
  | _ => throwError "#zx: not built from the `ZX` constructors:{indentExpr e}"

/-- Render an `Expr` as an algebraic ZX diagram, or `none` if it is not a
    `ZX n m` term (possibly under binders). The `#zx` command uses this to
    accept algebraic terms alongside graph-style `ZXDiagram`s.

    Leading `∀`s are instantiated with their own binders, so a diagram
    parameterized by a phase — `greenAlphaCircle : (α : AlgPhase) → ZX 0 0` —
    draws with `α` written beside the spider. -/
def zxTermHtml? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  forallTelescopeReducing (← inferType e) fun xs body => do
    if !isZXType (← whnf body) then return none
    return some (← zxSkelOfExpr (mkAppN e xs)).toHtml

/-- Render a goal `a ≈zx b` as its two sides side by side, or `none` if `e` is
    not a `≈zx` application at all. A side that is not built from the `ZX`
    constructors throws, just as `zxTermHtml?` does — the caller decides
    whether that is an error or simply nothing to draw.

    Unlike the graph-style `≈z` case in `SpLean/Panel.lean`, neither side is
    evaluated: an algebraic goal in mid-proof is usually open (`α β : AlgPhase`
    in the context), and the walker draws those phases as themselves. -/
def zxEquivHtml? (e : Expr) : MetaM (Option Html) := do
  let e ← instantiateMVars e
  let args := e.getAppArgs
  unless e.getAppFn.constName? == some ``ZX.Equiv && args.size == 4 do return none
  let lhs ← zxSkelOfExpr args[2]!
  let rhs ← zxSkelOfExpr args[3]!
  return some (lhs.toWire.toHtml (some rhs.toWire))

end SpLean.Algebraic
