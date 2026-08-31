import SpLean.Algebraic.ZX
import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Rules.Lemmas
import SpLean.Algebraic.Combinators
import SpLean.Algebraic.Reassoc

namespace SpLean.Algebraic

@[zx_reassoc]
theorem hadamard_hadamard :
    ZX.hadamard ≫ ZX.hadamard ≈zx ZX.wire := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, hadSem, sum_wires1]
  cases f 0 <;> cases g 0 <;> norm_num [inv_root_two_mul_self_complex]

@[zx_reassoc]
theorem hadamard_hadamard_n (n : ℕ):
    ZX.nHadamard n ≫ ZX.nHadamard n ≈zx ZX.nWire n := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem]
  simp only [n_hadamard_sem, hadSem, n_wire_sem]
  -- Split into f = g and ¬(f = g)
  split; rename_i h
  -- On f = g
  on_goal 1 =>
    -- Replace g with f
    subst h
    -- Work out the bit inside the sum
    have hprod : ∀ x : Wires n,
        (∏ i, if (f i && x i) = true then -((√2 : ℝ) : ℂ)⁻¹ else ((√2 : ℝ) : ℂ)⁻¹) *
          (∏ i, if (x i && f i) = true then -((√2 : ℝ) : ℂ)⁻¹ else ((√2 : ℝ) : ℂ)⁻¹)
        = (1 / 2 : ℂ) ^ n := by
      intro x
      -- Combine the two products
      rw [← Finset.prod_mul_distrib]
      -- Work out the bit inside the product
      have hi : ∀ i : Fin n,
          (if (f i && x i) = true then -((√2 : ℝ) : ℂ)⁻¹ else ((√2 : ℝ) : ℂ)⁻¹) *
            (if (x i && f i) = true then -((√2 : ℝ) : ℂ)⁻¹ else ((√2 : ℝ) : ℂ)⁻¹)
          = 1 / 2 := by
        intro i
        cases f i <;> cases x i <;> norm_num [inv_root_two_mul_self_complex]
      simp only [hi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp only [hprod]
    simp only [one_div, inv_pow]
    norm_num
  -- On ¬(f = g)
  rename_i h;
  -- Combine the two products
  simp only [← Finset.prod_mul_distrib]
  -- `f ≠ g` gives a wire `j` where they differ
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h ; clear h
  -- swap the sum over assignments with the product over wires:
  --   ∑ x, ∏ i, F i (x i) = ∏ i, ∑ b, F i b
  have hswap := Fintype.prod_sum (R := ℂ) (κ := fun _ : Fin n => Bool)
    (fun (i : Fin n) (b : Bool) =>
      (if (f i && b) = true then -((√2 : ℝ) : ℂ)⁻¹ else ((√2 : ℝ) : ℂ)⁻¹) *
        (if (b && g i) = true then -((√2 : ℝ) : ℂ)⁻¹ else ((√2 : ℝ) : ℂ)⁻¹))
  rw [← hswap] ; clear hswap
  -- the factor at `j` is `c * c + c * (-c) = 0`, so the whole product vanishes
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  cases hf : f j <;> cases hg : g j <;>
    simp_all only [ne_eq, not_true_eq_false] <;>
    norm_num
