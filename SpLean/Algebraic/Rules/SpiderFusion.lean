import SpLean.Algebraic.ZX
import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Rules.Lemmas
import SpLean.Algebraic.Rules.ColourChange
import SpLean.Algebraic.Tactics
import SpLean.Algebraic.Rules.Structural
import SpLean.Algebraic.Rules.HadamardHadamard
import SpLean.Algebraic.Reassoc

namespace SpLean.Algebraic

@[zx_reassoc]
theorem spider_fusion_Z_one_wire (n m : ℕ) (α β : AlgPhase) :
    (ZX.spider .Z n 1 α ≫ ZX.spider .Z 1 m β) ≈zx ZX.spider .Z n m (α + β) := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem]
  simp only [sum_wires1, zSpiderSem]
  norm_num
  simp only [ite_and]
  split_ifs <;> ring

@[zx_reassoc]
theorem spider_fusion_X_one_wire (n m : ℕ) (α β : AlgPhase) :
    (ZX.spider .X n 1 α ≫ ZX.spider .X 1 m β) ≈zx ZX.spider .X n m (α + β) := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem]
  simp only [sum_wires1, xSpiderSem, zSpiderSem, hadSem]
  norm_num
  -- Collapse the LHS sums: the negated branch needs splitting off with
  -- `sum_neg_distrib` before the endpoint lemmas can see it.
  simp only [sum_bool_endpoints, sum_bool_all_false, sum_bool_all_true]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp only [sum_bool_all_false, sum_bool_all_true]
  -- Collapse the RHS double sum: distribute so each `ite` is the whole summand.
  conv_rhs => simp only [mul_add, add_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  ring_nf
  simp only [sum_bool_endpoints₂]
  -- Both sides now mention the same four Hadamard products, so they never need
  -- expanding: (A+B)(C+D) + (A-B)(C-D) = 2(AC+BD), and the two ½s cancel it.
  rw [inv_root_two_sq_complex]
  ring

/-! ### Fusion along several wires
Fusion along k+1 wires, so that fusion along 0 wires (impossible!) is not representable -/

/-- Z spider fusion along `k + 1` parallel wires. -/
@[zx_reassoc]
theorem spider_fusion_Z (n m k : ℕ) (α β : AlgPhase) :
    (ZX.spider .Z n (k + 1) α ≫ ZX.spider .Z (k + 1) m β) ≈zx
      ZX.spider .Z n m (α + β) := by
  refine ⟨1, one_ne_zero, fun f h => ?_⟩
  rw [one_mul]
  simp only [ZX.sem]
  have key : ∀ g : Wires (k + 1),
      zSpiderSem α f g * zSpiderSem β g h =
        (if g = (fun _ => false) then
            (if (∀ i, f i = false) ∧ (∀ j, h j = false) then 1 else 0) else 0)
          + (if g = (fun _ => true) then
              α.expI * β.expI *
                (if (∀ i, f i = true) ∧ (∀ j, h j = true) then 1 else 0) else 0) := by
    intro g
    by_cases hgf : g = fun _ => false
    · subst hgf
      simp [zSpiderSem, ite_and, funext_iff]
      split_ifs <;> rfl
    · by_cases hgt : g = fun _ => true
      · subst hgt
        simp [zSpiderSem, ite_and, funext_iff]
        split_ifs <;> rfl
      · have h1 : ¬ ∀ x, g x = false := fun H => hgf (funext H)
        have h2 : ¬ ∀ x, g x = true := fun H => hgt (funext H)
        simp [zSpiderSem, hgf, hgt, h1, h2]
  simp only [key]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [zSpiderSem, ite_and]

/-- X spider fusion along `k + 1` parallel wires. -/
@[zx_reassoc]
theorem spider_fusion_X (n m k : ℕ) (α β : AlgPhase) :
    (ZX.spider .X n (k + 1) α ≫ ZX.spider .X (k + 1) m β) ≈zx ZX.spider .X n m (α + β) := by
  zx_rw [colour_change_X_Z]
  zx_rw [colour_change_X_Z]
  zx_assoc
  zx_rw [hadamard_hadamard_n_assoc]
  zx_rw [spider_fusion_Z_assoc]
  zx_rw [← colour_change_X_Z]

end SpLean.Algebraic
