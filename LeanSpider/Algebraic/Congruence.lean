import LeanSpider.Algebraic.Semantics

namespace LeanSpider.Algebraic

open Complex Matrix

/-- Z-spider matrices are equal whenever their phases denote the same
    complex number. -/
theorem Z_spiderMatrix_congr_phase {n m : Nat} {α β : AlgPhase}
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
theorem spider_phase_eq {c : SpiderColor} {n m : Nat} {α β : AlgPhase}
    (h : phaseToComplex α = phaseToComplex β) :
    ZX.spider c n m α ≃ZX ZX.spider c n m β := by
  show ZX.sem _ = ZX.sem _
  cases c with
  | Z => simp [ZX.sem, Z_spiderMatrix_congr_phase h]
  | X => rfl

/-- Convenience: `α = β` in `AlgPhase` is enough — no need to detour through
    `phaseToComplex`. Useful when the phase identity closes by `abel`/`ring`. -/
theorem spider_eq_of_phase_eq {c : SpiderColor} {n m : Nat} {α β : AlgPhase}
    (h : α = β) :
    ZX.spider c n m α ≃ZX ZX.spider c n m β := by
  subst h; rfl

/-- Mod-2π periodicity at the spider level: a spider's phase can be shifted by
    any integer multiple of `2` (i.e. by full turns) without changing its
    `≃ZX`-equivalence class. The renderer normalises phases mod-2π for display,
    so this lemma is what bridges the displayed form to the algebraic form. -/
theorem ZX.spider_phase_mod_two {c : SpiderColor} {n m : Nat}
    (α : AlgPhase) (k : ℤ) :
    ZX.spider c n m α ≃ZX ZX.spider c n m (α + 2 * (k : ℚ)) :=
  spider_phase_eq (phaseToComplex_add_two_mul_int α k).symm

/-- Compose respects `≃ZX` in both arguments.

    Used by `Quotient.lift₂` when defining `ZXQ.compose`, and useful in its
    own right for hand-rolled congruence proofs. -/
theorem ZX.compose_congr {n m k : Nat} {a a' : ZX n m} {b b' : ZX m k}
    (ha : a ≃ZX a') (hb : b ≃ZX b') : (a × b) ≃ZX (a' × b') := by
  show ZX.sem _ = ZX.sem _
  simp only [ZX.sem]
  rw [show a.sem = a'.sem from ha, show b.sem = b'.sem from hb]

/-- Stack respects `≃ZX` in both arguments.

    Currently trivial under the placeholder `stack` semantics (`.sem = 0`).
    Once `stack` semantics is filled in (Kronecker product), this will need
    a real proof; the *statement* will not change. -/
theorem ZX.stack_congr {n m p q : Nat} {a a' : ZX n m} {b b' : ZX p q}
    (_ha : a ≃ZX a') (_hb : b ≃ZX b') : (a ⊗ b) ≃ZX (a' ⊗ b') := by
  show ZX.sem _ = ZX.sem _
  simp only [ZX.sem]

/-- Composition is associative up to `≃ZX`.

    Follows from `Matrix.mul_assoc`: with the right-to-left compose
    convention, `((a × b) × c).sem = c.sem * (b.sem * a.sem)` and
    `(a × (b × c)).sem = (c.sem * b.sem) * a.sem`. -/
theorem ZX.compose_assoc {n m k l : Nat}
    (a : ZX n m) (b : ZX m k) (c : ZX k l) :
    ((a × b) × c) ≃ZX (a × (b × c)) := by
  show ZX.sem _ = ZX.sem _
  simp only [ZX.sem]
  exact (Matrix.mul_assoc c.sem b.sem a.sem).symm

end LeanSpider.Algebraic
