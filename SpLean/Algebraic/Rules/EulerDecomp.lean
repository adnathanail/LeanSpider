import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Rules.Lemmas
import SpLean.Algebraic.Reassoc

namespace SpLean.Algebraic

noncomputable abbrev eulerDecompScalar := Complex.exp (- (Complex.I * Real.pi / 4))

/-- The scalar for Euler decomp
    casted nicely for `hadSem` and `√2` lemmas in `Rules/Lemmas.lean` -/
theorem exp_neg_i_pi_over_four_eq :
    eulerDecompScalar = ((√2 : ℝ) : ℂ)⁻¹ - ((√2 : ℝ) : ℂ)⁻¹ * Complex.I := by
  unfold eulerDecompScalar
  rw [show (- (Complex.I * Real.pi / 4)) = ((-(Real.pi / 4) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four,
    ← inv_root_two_eq_div]
  push_cast
  ring

/-- Euler decomposition: `H = e^{-iπ/4} Z(π/2) ≫ X(π/2) ≫ Z(π/2)` -/
@[zx_reassoc]
theorem euler_decomp_ZXZ :
    ZX.hadamard
      ≈zx (ZX.spider .Z 1 1 (π/2) ≫ ZX.spider .X 1 1 (π/2) ≫ ZX.spider .Z 1 1 (π/2)) := by
  refine ⟨eulerDecompScalar, Complex.exp_ne_zero _, fun f g => ?_⟩
  simp only [ZX.sem, hadSem, zSpiderSem, xSpiderSem, sum_wires1]
  norm_num
  cases f 0 <;> cases g 0 <;>
    simp only [and_true, Bool.false_eq_true, and_false, ↓reduceIte] <;>
    field_simp
  all_goals
    rw [exp_neg_i_pi_over_four_eq,
        show ((√2 : ℝ) : ℂ)⁻¹ = ((√2 / 2 : ℝ) : ℂ) by
          rw [← Complex.ofReal_inv, inv_root_two_eq_div]]
    apply Complex.ext <;> norm_num <;> ring

/-- Euler decomposition with the colours swapped:
`H = X(π/2) ≫ Z(π/2) ≫ X(π/2)`, up to a scalar. -/
@[zx_reassoc]
theorem euler_decomp_XZX :
    ZX.hadamard
      ≈zx (ZX.spider .X 1 1 (π/2) ≫ ZX.spider .Z 1 1 (π/2) ≫ ZX.spider .X 1 1 (π/2)) := by
  refine ⟨eulerDecompScalar, Complex.exp_ne_zero _, fun f g => ?_⟩
  simp only [ZX.sem, hadSem, zSpiderSem, xSpiderSem, sum_wires1]
  norm_num
  cases f 0 <;> cases g 0 <;>
    simp only [↓reduceIte, Bool.false_eq_true, and_false, and_true] <;>
    field_simp
  all_goals
    rw [exp_neg_i_pi_over_four_eq,
        show ((√2 : ℝ) : ℂ) ^ 3 = 2 * ((√2 : ℝ) : ℂ) by
          norm_cast
          rw [pow_succ, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)],
        show ((√2 : ℝ) : ℂ)⁻¹ = ((√2 / 2 : ℝ) : ℂ) by
          rw [← Complex.ofReal_inv, inv_root_two_eq_div]]
    apply Complex.ext <;> norm_num [pow_succ] ; ring

end SpLean.Algebraic
