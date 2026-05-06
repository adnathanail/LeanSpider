import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import LeanSpider.ZXDiagram

namespace LeanSpider.Algebraic

open Complex

/-- Interpret a `Phase` (rational multiple of π) as a unit complex number.
    `phaseToComplex ⟨p, q⟩ = exp(i · π · p / q)`. -/
noncomputable def phaseToComplex (φ : Phase) : ℂ :=
  Complex.exp (Complex.I * Real.pi * (φ.num : ℂ) / (φ.den : ℂ))

/-- Adding phases multiplies the corresponding complex numbers.
    `Phase.den : ℕ+` rules out `den = 0` at the type level, so no side
    hypothesis is needed. -/
theorem phaseToComplex_add (a b : Phase) :
    phaseToComplex (a + b) = phaseToComplex a * phaseToComplex b := by
  unfold phaseToComplex
  show Complex.exp (Complex.I * Real.pi
          * ((a.num * (b.den : Int) + b.num * (a.den : Int) : Int) : ℂ)
          / (((a.den * b.den : ℕ+) : Nat) : ℂ))
      = Complex.exp (Complex.I * Real.pi * (a.num : ℂ) / ((a.den : Nat) : ℂ))
        * Complex.exp (Complex.I * Real.pi * (b.num : ℂ) / ((b.den : Nat) : ℂ))
  rw [← Complex.exp_add]
  congr 1
  have ha' : ((a.den : Nat) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr a.den.pos.ne'
  have hb' : ((b.den : Nat) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr b.den.pos.ne'
  push_cast
  field_simp

end LeanSpider.Algebraic
