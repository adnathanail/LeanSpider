import SpLean.Algebraic

open SpLean.Algebraic

example {n m : ℕ} (a : ZX n m) : (a ⊗ .empty) ≈zx a := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, mul_one]
  rfl
