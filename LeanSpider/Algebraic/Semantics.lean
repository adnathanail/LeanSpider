import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import LeanSpider.Algebraic.Phase
import LeanSpider.Algebraic.ZX

namespace LeanSpider.Algebraic

open Complex Matrix

/-- The Z-spider matrix: `|0…0⟩⟨0…0| + e^{iφ}·|1…1⟩⟨1…1|`.

    Rows are outputs (`Fin (2^m)`), columns are inputs (`Fin (2^n)`).
    The all-zeros basis vector lives at index `0`, the all-ones at `2^k - 1`.

    Written as a sum of two indicators (rather than nested `if`s) so the
    `n = m = 0` corner case correctly evaluates to `1 + e^{iφ}` — both
    indices collide at `0` there, and the spider is a scalar. -/
noncomputable def Z_spiderMatrix (n m : Nat) (φ : AlgPhase) :
    Matrix (Fin (2^m)) (Fin (2^n)) ℂ :=
  fun j i =>
    (if i.val = 0 ∧ j.val = 0 then (1 : ℂ) else 0) +
    (if i.val = 2^n - 1 ∧ j.val = 2^m - 1 then phaseToComplex φ else 0)

/-- Denotational interpretation of a `ZX n m` term as a `2^m × 2^n` complex matrix.

    Convention: `compose a b` is read "first `a`, then `b`" so the matrix product
    is `⟦b⟧ * ⟦a⟧` (matrices act right-to-left).

    NOTE: only the Z-spider, compose, and identity-like cases (`empty`, `wire`)
    are given their true semantics here.  `hadamard`, `spider .X`, and `stack`
    use placeholder `0` matrices for now — the Z-spider fusion proof in
    `SpiderFusion.lean` does not unfold these branches.  Filling them in is
    tracked as future work (it requires Kronecker-product reindexing for
    `stack`, and a Hadamard-sandwich definition for `spider .X`). -/
noncomputable def ZX.sem : {n m : Nat} → ZX n m → Matrix (Fin (2^m)) (Fin (2^n)) ℂ
  | _, _, ZX.empty            => 1  -- Identity on 1 dimension
  | _, _, ZX.wire             => 1  -- Identity on 2 dimensions
  | _, _, ZX.hadamard         => 0  -- TODO: ![![1, 1], ![1, -1]] / √2 once needed
  | _, _, ZX.spider .Z n m φ  => Z_spiderMatrix n m φ
  | _, _, ZX.spider .X _ _ _  => 0  -- TODO: H-sandwich of Z-spider once stack is wired up
  | _, _, ZX.stack _ _        => 0  -- TODO: Kronecker product with Fin (2^(n+p)) reindex
  | _, _, ZX.compose a b      => b.sem * a.sem

/-- Semantic equivalence of ZX terms: equal denotations as complex matrices.

    Marked `@[reducible]` so `rw` and `exact` see through it to the underlying
    `Eq` of matrices — this lets named ZX rules like `Z_spiderFusion` be applied
    directly with `rw`. -/
@[reducible] def ZX.equiv {n m : Nat} (a b : ZX n m) : Prop := a.sem = b.sem

scoped infix:50 " ≃ZX " => ZX.equiv

@[refl] theorem ZX.equiv_refl {n m : Nat} (a : ZX n m) : a ≃ZX a := rfl

theorem ZX.equiv_symm {n m : Nat} {a b : ZX n m} : a ≃ZX b → b ≃ZX a := Eq.symm

theorem ZX.equiv_trans {n m : Nat} {a b c : ZX n m} : a ≃ZX b → b ≃ZX c → a ≃ZX c :=
  Eq.trans

end LeanSpider.Algebraic
