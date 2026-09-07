import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Combinators
import SpLean.Algebraic.Rules.Structural

namespace SpLean.Algebraic

/-- Self-loop on a Z spider vanishes. -/
theorem zSpider_self_loop (n m : ℕ) (α : AlgPhase) :
    (ZX.spider .Z n (m + 2) α ≫ (ZX.nWire m ⊗ ZX.cap)) ≈zx ZX.spider .Z n m α := by
  refine ⟨1, one_ne_zero, fun f h => ?_⟩
  rw [one_mul]
  simp only [ZX.sem]
  have hsplit : ∀ F : Wires (m + 2) → ℂ,
      ∑ g : Wires (m + 2), F g = ∑ p : Wires m, ∑ q : Wires 2, F (Fin.append p q) := by
    intro F
    rw [← Equiv.sum_comp (Fin.appendEquiv m 2) F, Fintype.sum_prod_type]
    trivial
  rw [hsplit]
  simp only [Fin.append_left, Fin.append_right, nWire_sem]
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hv : (fun j : Fin m => h (Fin.castAdd 0 j)) = h := by funext j; rfl
  rw [hv]
  have key : ∀ q : Wires 2,
      zSpiderSem α f (Fin.append h q) * zSpiderSem 0 q (fun j => h (Fin.natAdd m j)) =
        (if q = (fun _ => false) then
            (if (∀ i, f i = false) ∧ (∀ j, h j = false) then 1 else 0)
          else 0)
          + if q = (fun _ => true) then
              α.expI * (if (∀ i, f i = true) ∧ (∀ j, h j = true) then 1 else 0)
            else 0 := by
    intro q
    by_cases hqf : q = fun _ => false
    · subst hqf
      simp only [zSpiderSem]
      norm_num
      simp only [Fin.forall_fin_add, Fin.append_left, Fin.append_right, and_true,Bool.false_eq_true, forall_const, and_false]
      tauto
    · by_cases hqt : q = fun _ => true
      · subst hqt
        simp only [zSpiderSem]
        norm_num
        simp only [Fin.forall_fin_add, Fin.append_left, Fin.append_right, Bool.true_eq_false, forall_const, and_false, ↓reduceIte, ite_and, zero_add, right_eq_add, ite_eq_right_iff]
        simp_all only [Fin.castAdd_zero, Fin.cast_eq_self, IsEmpty.forall_iff]
      · have h1 : ¬ ∀ i, q i = false := fun H => hqf (funext H)
        have h2 : ¬ ∀ i, q i = true := fun H => hqt (funext H)
        simp only [zSpiderSem, h1, h2]
        norm_num [Nat.add_zero]
        simp_all only [↓reduceIte, add_zero]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [zSpiderSem]

/-- Self-loop through a Hadamard on a Z spider vanishes and adds π to the phase. -/
theorem zSpider_hadamard_self_loop (n m : ℕ) (α : AlgPhase) :
    (ZX.spider .Z n (m + 2) α ≫ (ZX.nWire m ⊗ (ZX.hadamard ⊗ ZX.wire)) ≫ (ZX.nWire m ⊗ ZX.cap))
      ≈zx ZX.spider .Z n m (α + π) := by
  sorry

/-- A plain self-loop on an X spider vanishes. The cap has to be an X cap:
closing two legs of an X spider with a *Z* cap is a Hopf redex
(`Rules/Hopf.lean`), not a self-loop. -/
theorem xSpider_self_loop (n m : ℕ) (α : AlgPhase) :
    (ZX.spider .X n (m + 2) α ≫ (ZX.nWire m ⊗ ZX.capX)) ≈zx ZX.spider .X n m α := by
  sorry

/-- A self-loop through a Hadamard on an X spider vanishes and adds π to the
phase. -/
theorem xSpider_hadamard_self_loop (n m : ℕ) (α : AlgPhase) :
    (ZX.spider .X n (m + 2) α ≫ (ZX.nWire m ⊗ (ZX.hadamard ⊗ ZX.wire))
        ≫ (ZX.nWire m ⊗ ZX.capX))
      ≈zx ZX.spider .X n m (α + π) := by
  sorry

end SpLean.Algebraic
