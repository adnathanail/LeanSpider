import SpLean.Algebraic.Rules.Structural
import SpLean.Algebraic.Tactics
import Mathlib.Util.AddRelatedDecl

/-!
# The `@[zx_reassoc]` attribute

`zx_rw` rewrites a goal *in place*, so a rule only fires where its left-hand
side appears literally. `hadamard_hadamard`'s LHS is `hadamard ≫ hadamard`, and
in `hadamard ≫ (hadamard ≫ c)` there is no such subterm — the redex straddles
the bracketing. That is what `SemanticsTesting/09Rules.lean` spends its
`compose_assoc` lines fixing by hand.

The fix is the one Mathlib's category theory library uses (`Mathlib/Tactic/
CategoryTheory/Reassoc.lean`): keep every composition right-nested, and give
each rule a *whiskered* variant that already matches that shape.
`@[zx_reassoc] theorem F : a ≈zx b` generates

    F_assoc : ∀ .. {k} (c : ZX m k), a ≫ c ≈zx b ≫ c

with both sides re-nested to the right and any `wire` a rewrite left behind
absorbed, so `hadamard_hadamard` yields

    hadamard_hadamard_assoc : hadamard ≫ (hadamard ≫ c) ≈zx c

Both lemmas are kept, because a redex at the *tail* of a chain has no `c` to
whisker over: `x ≫ (hadamard ≫ hadamard)` needs the plain rule, and
`x ≫ (hadamard ≫ (hadamard ≫ y))` needs the `_assoc` one. Mathlib keeps both
for the same reason.

The generated proof is built directly rather than by `simp`: `simp` needs `Eq`,
and `compose_assoc` is an `≈zx`. `nest` below does that job, returning a proof
alongside the re-nested term.
-/

open Lean Meta Elab Term Mathlib.Tactic

namespace SpLean.Algebraic.Reassoc

/-- Right-nest a composition.

Given `a : ZX n m` and `c : ZX m k`, return the right-nested form `d` of
`a ≫ c` together with a proof that `a ≫ c ≈zx d`.

The `wire` cases are the analogue of Mathlib's `Category.id_comp`/`comp_id`
cleanup: a rule whose RHS is `wire` (`hadamard_hadamard`) or `nWire n`
(`hadamard_hadamard_n`) would otherwise generate a variant ending in a stray
`wire ≫ c`. -/
partial def nest (a c : Expr) : MetaM (Expr × Expr) := do
  match_expr a with
  | ZX.compose _n _m _k x y =>
    -- `(x ≫ y) ≫ c ≈zx x ≫ (y ≫ c) ≈zx x ≫ d₁ ≈zx d`
    let (d₁, py) ← nest y c
    let (d, px) ← nest x d₁
    let pAssoc ← mkAppM ``compose_assoc #[x, y, c]
    let pCongr ← mkAppM ``ZX.Equiv.compose_congr #[← mkAppM ``ZX.Equiv.refl #[x], py]
    let p ← mkAppM ``ZX.Equiv.trans #[pAssoc, ← mkAppM ``ZX.Equiv.trans #[pCongr, px]]
    return (d, p)
  | ZX.wire => return (c, ← mkAppM ``wire_compose #[c])
  | ZX.nWire _n => return (c, ← mkAppM ``nWire_compose #[c])
  | _ =>
    match_expr c with
    | ZX.wire => return (a, ← mkAppM ``compose_wire #[a])
    | ZX.nWire _m => return (a, ← mkAppM ``compose_nWire #[a])
    | _ =>
      let d ← mkAppM ``ZX.compose #[a, c]
      return (d, ← mkAppM ``ZX.Equiv.refl #[d])

/-- Build the whiskered, right-nested variant of a proof of `∀ .., a ≈zx b`. -/
def reassocExpr (pf : Expr) : MetaM Expr := do
  forallTelescope (← inferType pf) fun xs body => do
    let pf := mkAppN pf xs
    let_expr ZX.Equiv _n m a b := body
      | throwError "`zx_reassoc` expects a rule of the form `a ≈zx b`, not{indentExpr body}"
    withLocalDecl `k .implicit (mkConst ``Nat) fun k =>
      withLocalDeclD `c (mkAppN (mkConst ``ZX) #[m, k]) fun c => do
        -- `pl : a ≫ c ≈zx lhs`, `pr : b ≫ c ≈zx rhs`
        let (_, pl) ← nest a c
        let (_, pr) ← nest b c
        -- `pw : a ≫ c ≈zx b ≫ c`
        let pw ← mkAppM ``ZX.Equiv.compose_congr #[pf, ← mkAppM ``ZX.Equiv.refl #[c]]
        let p ← mkAppM ``ZX.Equiv.trans
          #[← mkAppM ``ZX.Equiv.symm #[pl], ← mkAppM ``ZX.Equiv.trans #[pw, pr]]
        mkLambdaFVars (xs ++ #[k, c]) p

/-- Adding `@[zx_reassoc]` to a rule `F : ∀ .., a ≈zx b` generates `F_assoc`,
the same rule whiskered by a trailing `c` and re-nested to the right, so that it
fires inside an already right-nested composition. See the module docstring. -/
syntax (name := zx_reassoc) "zx_reassoc" optAttrArg : attr

initialize registerBuiltinAttribute {
  name := `zx_reassoc
  descr := "Generate the right-nested whiskered variant `F_assoc` of a `≈zx` rule `F`."
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
    | `(attr| zx_reassoc $optAttr) => MetaM.run' do
      unless kind == AttributeKind.global do
        throwError "`zx_reassoc` can only be used as a global attribute"
      addRelatedDecl src (src.appendAfter "_assoc") ref optAttr fun value levels =>
        Term.TermElabM.run' <| Term.withSynthesize do
          pure (← reassocExpr value, levels)
    | _ => throwUnsupportedSyntax }

end SpLean.Algebraic.Reassoc

namespace SpLean.Algebraic

/-- Right-nest every composition in the goal.

`grw [compose_assoc]` fires at every occurrence at once, so repeating it to
fixpoint reaches the normal form that `@[zx_reassoc]` rules are stated against.
This replaces the hand-aimed `zx_rw [compose_assoc ..]` lines that used to be
needed to expose a redex. -/
macro "zx_assoc" : tactic => `(tactic| repeat grw [compose_assoc])

end SpLean.Algebraic
