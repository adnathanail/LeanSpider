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

/-- Format an `AlgPhase` directly from its ℚ `num`/`den` (no mod-2π
    reduction — that's why we don't route through the graph-side
    `Phase.format`). ℚ is already in lowest terms by construction, so
    `phaseLit 2 4` formats as `π/2`; `phaseLit 9 2` formats as `9π/2`.
    Negative numerators carry the sign in `num`. -/
def AlgPhase.format (q : AlgPhase) : String :=
  let n := q.num
  let d := q.den
  if n = 0 then "0"
  else if d = 1 then
    if n =  1 then "π"
    else if n = -1 then "-π"
    else s!"{n}π"
  else if n =  1 then s!"π/{d}"
  else if n = -1 then s!"-π/{d}"
  else s!"{n}π/{d}"

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

/-- Mod-2π periodicity: shifting a phase by an integer multiple of `2` (a full
    turn, since phases are rational multiples of π) leaves its complex
    interpretation unchanged. -/
theorem phaseToComplex_add_two_mul_int (α : AlgPhase) (k : ℤ) :
    phaseToComplex (α + 2 * (k : ℚ)) = phaseToComplex α := by
  unfold phaseToComplex
  push_cast
  rw [show Complex.I * Real.pi * ((α : ℂ) + 2 * (k : ℂ))
        = Complex.I * Real.pi * (α : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I)
        from by ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end LeanSpider.Algebraic
