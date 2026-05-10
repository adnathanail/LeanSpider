import LeanSpider.Algebraic.Semantics

namespace LeanSpider.Algebraic

open Complex Matrix

/-- Two phases denote the same complex number iff their fractions are equal
    as integers (cross-multiplied). The numerator/denominator pair `⟨p, q⟩`
    represents `p/q`, and `phaseToComplex` collapses fractions equal modulo
    rational simplification. -/
theorem congr_phase {a b : Phase}
    (h : a.num * (b.den : Int) = b.num * (a.den : Int)) :
    phaseToComplex a = phaseToComplex b := by
  unfold phaseToComplex
  congr 1
  -- Change division equality to multiplication equality
  field_simp
  -- Swap order of multiplication arguments
  rw [mul_comm (a.den : ℂ) (b.num : ℂ)]
  -- Apply hypothesis h, dealing with type casting
  exact_mod_cast h

/-- Z-spider matrices are equal whenever their phases denote the same
    complex number. -/
theorem Z_spiderMatrix_congr_phase {n m : Nat} {α β : Phase}
    (h : phaseToComplex α = phaseToComplex β) :
    Z_spiderMatrix n m α = Z_spiderMatrix n m β := by
  unfold Z_spiderMatrix
  ext j i
  congr 2

/-- A spider's `≃ZX`-class is determined by `phaseToComplex` of its phase —
    i.e. equal phases (modulo `2π`) give equivalent spiders.

    For `c = .Z` this follows from `Z_spiderMatrix_congr_phase`. For `c = .X`,
    `ZX.sem` is currently the placeholder `0` so the lemma is trivial; it will
    need re-proving once X-spider semantics is implemented. -/
theorem spider_phase_eq {c : SpiderColor} {n m : Nat} {α β : Phase}
    (h : phaseToComplex α = phaseToComplex β) :
    ZX.spider c n m α ≃ZX ZX.spider c n m β := by
  show ZX.sem _ = ZX.sem _
  cases c with
  | Z => simp [ZX.sem, Z_spiderMatrix_congr_phase h]
  | X => rfl

end LeanSpider.Algebraic
