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
  rw [sum_wires2]
  simp only [zSpiderSem, Fin.forall_fin_add]
  norm_num
  ring

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
