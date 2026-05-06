import Mathlib.Tactic.FinCases
import LeanSpider.Algebraic.Semantics

namespace LeanSpider.Algebraic

open Complex Matrix

/-- The `(s = 0)`-row of an `n → 1` Z-spider: a `1` at the all-zeros input,
    `0` elsewhere. -/
private lemma Z_spider_n1_apply_zero (n : Nat) (α : Phase) (i : Fin (2^n)) :
    Z_spiderMatrix n 1 α 0 i = if i.val = 0 then (1 : ℂ) else 0 := by
  simp [Z_spiderMatrix]

/-- The `(s = 1)`-row of an `n → 1` Z-spider: `phase α` at the all-ones input,
    `0` elsewhere. -/
private lemma Z_spider_n1_apply_one (n : Nat) (α : Phase) (i : Fin (2^n)) :
    Z_spiderMatrix n 1 α 1 i = if i.val = 2^n - 1 then phaseToComplex α else 0 := by
  simp [Z_spiderMatrix]

/-- The `(s = 0)`-column of a `1 → k` Z-spider: a `1` at the all-zeros output,
    `0` elsewhere. -/
private lemma Z_spider_1k_apply_zero (k : Nat) (β : Phase) (j : Fin (2^k)) :
    Z_spiderMatrix 1 k β j 0 = if j.val = 0 then (1 : ℂ) else 0 := by
  simp [Z_spiderMatrix]

/-- The `(s = 1)`-column of a `1 → k` Z-spider: `phase β` at the all-ones
    output, `0` elsewhere. -/
private lemma Z_spider_1k_apply_one (k : Nat) (β : Phase) (j : Fin (2^k)) :
    Z_spiderMatrix 1 k β j 1 = if j.val = 2^k - 1 then phaseToComplex β else 0 := by
  simp [Z_spiderMatrix]

/-- Two same-colour Z-spiders connected by a single wire fuse into one
    Z-spider with phases summed.  Stated for the cleanest swap-free form;
    the general multi-leg fusion follows by stacking with identity wires
    (out of scope for this milestone). -/
theorem Z_spiderFusion (n k : Nat) (α β : Phase) (hα : α.den ≠ 0) (hβ : β.den ≠ 0) :
    (ZX.spider .Z n 1 α ⨾ ZX.spider .Z 1 k β) ≃ZX ZX.spider .Z n k (α + β) := by
  -- Ask Lean to restate ≃ZX into its definition:
  --   that the semantic matrixes are equal
  show ZX.sem _ = ZX.sem _
  -- Rewrite the generic semantic function into the specific semantics
  --   for our inputs, namely the Z spider matrix function
  simp only [ZX.sem]
  -- Restate the matrix equalities as equalities of each cell in the matrix
  -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Defs.html#Matrix.ext
  ext j i
  -- Rewrite getting an element from the result of a matrix multiplication,
  --   into a sum of multiplications of elements from each matrix
  -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Matrix/Mul.html#Matrix.mul_apply
  rw [Matrix.mul_apply]
  -- The middle dimension `Fin (2^1)` is definitionally `Fin 2`; force that.
  show (∑ s : Fin 2, Z_spiderMatrix 1 k β j s * Z_spiderMatrix n 1 α s i)
      = Z_spiderMatrix n k (α + β) j i
  -- Rewrite sum over 2 element index as an explicit sum of 2 items
  -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Fin.html#Fin.sum_univ_two
  rw [Fin.sum_univ_two]
  -- Rewrite each Z spider matrix function call into if statements depending on indexes
  rw [Z_spider_n1_apply_zero, Z_spider_n1_apply_one,
      Z_spider_1k_apply_zero, Z_spider_1k_apply_one]
  -- Push the `*` inside each `if`, collapsing `(if h₁ ...) * (if h₂ ...)` to
  -- `if h₁ ∧ h₂ then a*b else 0`.  `simp` distributes `mul_ite` first, so the
  -- resulting AND has `i` on the outside — matching the RHS's `i ∧ j` order.
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, ← ite_and]
  -- Unfold RHS spider
  unfold Z_spiderMatrix
  -- Swap order of beta and alpha phases on LHS to match RHS
  --   (second spider comes first in B * A)
  rw [mul_comm (phaseToComplex β) (phaseToComplex α)]
  -- Adding phase parameters is equivalent to multiplying the resulting phases
  rw [show phaseToComplex (α + β) = phaseToComplex α * phaseToComplex β from
        phaseToComplex_add α β hα hβ]

end LeanSpider.Algebraic
