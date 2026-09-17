import SpLean.Algebraic.Equiv
import SpLean.Panel

namespace SpLean.Algebraic

def strongCompLHS : ZX 2 2 := .spider .X 2 1 ≫ .spider .Z 1 2
#zx strongCompLHS

def strongCompRHS : ZX 2 2 := (.spider .Z 1 2 ⊗ .spider .Z 1 2 : ZX 2 4) ≫ (.wire ⊗ .swap ⊗ .wire : ZX 4 4) ≫ (.spider .X 2 1 ⊗ .spider .X 2 1)
#zx strongCompRHS

noncomputable abbrev strongCompScalar (n m : ℕ) : Complex := Real.sqrt 2 ^ ((n - 1) * (m - 1))

lemma strongCompScalar_ne_zero (n m : ℕ) :
    strongCompScalar n m ≠ 0 := by
  unfold strongCompScalar
  norm_num

theorem strong_complementarity_2 :
    strongCompLHS ≈zx strongCompRHS := by
  refine ⟨strongCompScalar 2 2, strongCompScalar_ne_zero 2 2, fun f g => ?_⟩
