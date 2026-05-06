import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import LeanSpider.ZXDiagram

namespace LeanSpider.Algebraic

open Complex

/-- Interpret a `Phase` (rational multiple of π) as a unit complex number.
    `phaseToComplex ⟨p, q⟩ = exp(i · π · p / q)`. -/
noncomputable def phaseToComplex (φ : Phase) : ℂ :=
  Complex.exp (Complex.I * Real.pi * (φ.num : ℂ) / (φ.den : ℂ))

/-- Adding phases multiplies the corresponding complex numbers, when both
    denominators are nonzero. The hypothesis is needed because in Lean's reals
    `x / 0 = 0`, which would otherwise let pathological `Phase` values break
    the homomorphism. -/
theorem phaseToComplex_add (a b : Phase) (ha : a.den ≠ 0) (hb : b.den ≠ 0) :
    phaseToComplex (a + b) = phaseToComplex a * phaseToComplex b := by
  unfold phaseToComplex
  show Complex.exp (Complex.I * Real.pi * ((a.num * b.den + b.num * a.den : Int) : ℂ)
        / ((a.den * b.den : Nat) : ℂ))
      = Complex.exp (Complex.I * Real.pi * (a.num : ℂ) / (a.den : ℂ))
        * Complex.exp (Complex.I * Real.pi * (b.num : ℂ) / (b.den : ℂ))
  rw [← Complex.exp_add]
  congr 1
  have ha' : (a.den : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hb' : (b.den : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  push_cast
  field_simp

end LeanSpider.Algebraic
