import SpLean.Algebraic.ZX
import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Combinators
import SpLean.Algebraic.Rules.Structural
import SpLean.Algebraic.Rules.Lemmas

namespace SpLean.Algebraic

/-- `ZX.swap` is its own inverse. -/
theorem swap_swap : (ZX.swap ≫ ZX.swap) ≈zx ZX.nWire 2 := by
  refine ⟨1, one_ne_zero, fun f h => ?_⟩
  rw [one_mul, nWire_sem]
  have hfh : (f = h) ↔ (f 0 = h 0 ∧ f 1 = h 1) := by
    rw [funext_iff, Fin.forall_fin_two]
  simp only [ZX.sem, sum_wires2, hfh, Matrix.cons_val_zero, Matrix.cons_val_one]
  cases hf0 : f 0 <;> cases hf1 : f 1 <;> cases hh0 : h 0 <;> cases hh1 : h 1 <;>
    simp_all <;> decide

end SpLean.Algebraic
