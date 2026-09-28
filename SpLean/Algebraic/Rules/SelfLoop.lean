import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Combinators
import SpLean.Algebraic.Rules.Structural

namespace SpLean.Algebraic

/-- A Z spider with its last two legs closed off by any `k : ZX 2 0`. The
spider only ever feeds `k` the all-`false` or the all-`true` pair, so `k`
contributes just those two amplitudes, one weighting each branch of the
spider. Every Z self-loop rule is this with a particular `k`. -/
theorem zSpider_loop_sem {n m : ℕ} (α : AlgPhase) (k : ZX 2 0) (f : Wires n) (h : Wires m) :
    (ZX.spider .Z n (m + 2) α ≫ (ZX.nWire m ⊗ k)).sem f h =
      (if (∀ i, f i = false) ∧ (∀ j, h j = false) then k.sem (fun _ => false) ![] else 0)
        + α.expI *
          (if (∀ i, f i = true) ∧ (∀ j, h j = true) then k.sem (fun _ => true) ![] else 0) := by
  simp only [ZX.sem, sum_wires_append, Fin.append_left, Fin.append_right, nWire_sem,
    ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  eta_reduce
  have hv : (fun j : Fin m => h (Fin.castAdd 0 j)) = h := rfl
  have he : (fun j : Fin 0 => h (Fin.natAdd m j)) = ![] := by exact Matrix.empty_eq fun j => h (Fin.natAdd m j)
  rw [hv, he]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  simp only [zSpiderSem, Fin.forall_fin_add, Fin.append_left, Fin.append_right, add_mul,
    Finset.sum_add_distrib, ← and_assoc, ite_and, ite_mul, one_mul, zero_mul, mul_assoc,
    Finset.sum_ite_irrel, Finset.sum_const_zero, sum_bool_all_false, sum_bool_all_true,
    mul_ite, mul_zero]

/-- A cap with a Hadamard on one leg is the Hadamard matrix, read as an effect. -/
theorem hadamard_cap_sem (q : Wires 2) (e : Wires 0) :
    ((ZX.hadamard ⊗ ZX.wire) ≫ ZX.cap).sem q e = hadSem (q 0) (q 1) := by
  simp only [ZX.sem]
  rw [sum_wires2]
  cases h0 : q 0 <;> cases h1 : q 1 <;> simp [zSpiderSem, Fin.forall_fin_two, h0, h1]

/-- Self-loop on a Z spider vanishes. -/
theorem zSpider_self_loop (n m : ℕ) (α : AlgPhase) :
    (ZX.spider .Z n (m + 2) α ≫ (ZX.nWire m ⊗ ZX.cap)) ≈zx ZX.spider .Z n m α := by
  refine ⟨1, one_ne_zero, fun f h => ?_⟩
  rw [zSpider_loop_sem]
  simp [ZX.sem, zSpiderSem]

/-- Self-loop through a Hadamard on a Z spider vanishes and adds π to the phase.
The Hadamard weights the two branches `1/√2` and `-1/√2`: the `1/√2` is the
scalar, the sign is the `π`. -/
theorem zSpider_hadamard_self_loop (n m : ℕ) (α : AlgPhase) :
    (ZX.spider .Z n (m + 2) α ≫ (ZX.nWire m ⊗ (ZX.hadamard ⊗ ZX.wire)) ≫ (ZX.nWire m ⊗ ZX.cap))
      ≈zx ZX.spider .Z n m (α + π) := by
  zx_rw [stack_compose_interchange, nWire_compose]
  refine ⟨((Real.sqrt 2 : ℝ) : ℂ)⁻¹, by simp, fun f h => ?_⟩
  rw [zSpider_loop_sem, hadamard_cap_sem, hadamard_cap_sem]
  simp [ZX.sem, hadSem, zSpiderSem, mul_add, mul_ite, mul_comm]

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
