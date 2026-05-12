import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Rat.Cast.Defs

namespace LeanSpider.Algebraic

open Complex

/-- Algebraic phase: a rational multiple of π. The full `AddCommGroup` structure
    of `ℚ` is inherited automatically, so identities like
    `α + (-α) + α = α` close by `abel`, and any polynomial phase equality is
    discharged by `ring` / `field_simp` / `norm_num`.

    Semantic equality is mod-2π — captured by `phaseToComplex_periodic` rather
    than baked into definitional equality (which would force a quotient and
    make the type `noncomputable`, breaking widget rendering for concrete
    phases). -/
abbrev AlgPhase : Type := ℚ

/-- Build an `AlgPhase` literal from numerator and denominator:
    `phaseLit 1 2 = π/2`, `phaseLit (-1) 4 = -π/4`. -/
def phaseLit (p q : Int) : AlgPhase := (p : ℚ) / (q : ℚ)

/-- Interpret an `AlgPhase` (rational multiple of π) as a unit complex number:
    `phaseToComplex φ = exp(i · π · φ)`. -/
noncomputable def phaseToComplex (φ : AlgPhase) : ℂ :=
  Complex.exp (Complex.I * Real.pi * (φ : ℂ))

/-- Adding phases multiplies the corresponding complex numbers. -/
theorem phaseToComplex_add (a b : AlgPhase) :
    phaseToComplex (a + b) = phaseToComplex a * phaseToComplex b := by
  unfold phaseToComplex
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end LeanSpider.Algebraic
