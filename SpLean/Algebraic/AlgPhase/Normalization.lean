import SpLean.Algebraic.AlgPhase.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace AlgPhase

/-!
## Reduction of rationals to [0, 2)
-/

/- A phase is a *rational multiple of π*:
  the rational `q` denotes the angle `q·π`, so `1/2` is `π/2` and the period is `q ↦ q + 2`. -/
def red (q : ℚ) : ℚ := q - 2 * ⌊q / 2⌋

theorem red_nonneg (q : ℚ) : 0 ≤ red q := by
  have h : ((⌊q / 2⌋ : ℤ) : ℚ) ≤ q / 2 := Int.floor_le _
  unfold red
  linarith

theorem red_lt_two (q : ℚ) : red q < 2 := by
  have h : q / 2 < ((⌊q / 2⌋ : ℤ) : ℚ) + 1 := Int.lt_floor_add_one _
  unfold red
  linarith

/-- `red` is the identity on the `[0, 2)`. -/
theorem red_of_mem (q : ℚ) (h0 : 0 ≤ q) (h2 : q < 2) : red q = q := by
  have hz : ⌊q / 2⌋ = 0 := by
    rw [Int.floor_eq_zero_iff, Set.mem_Ico]
    constructor <;> linarith
  unfold red
  rw [hz]
  push_cast
  ring

@[simp] theorem red_idem (q : ℚ) : red (red q) = red q :=
  red_of_mem _ (red_nonneg q) (red_lt_two q)

theorem red_add_two_mul_int (q : ℚ) (n : ℤ) : red (q + 2 * (n : ℚ)) = red q := by
  unfold red
  have h : (q + 2 * (n : ℚ)) / 2 = q / 2 + (n : ℚ) := by ring
  rw [h, Int.floor_add_intCast]
  push_cast
  ring

/-- Reducing an operand first doesn't change the reduced sum. -/
theorem red_add_left (a b : ℚ) : red (red a + b) = red (a + b) := by
  have h : red a + b = (a + b) + 2 * ((-⌊a / 2⌋ : ℤ) : ℚ) := by
    unfold red; push_cast; ring
  rw [h, red_add_two_mul_int]

theorem red_add_right (a b : ℚ) : red (a + red b) = red (a + b) := by
  rw [add_comm a (red b), red_add_left, add_comm]

@[simp] theorem red_zero : red (0 : ℚ) = 0 := red_of_mem 0 le_rfl (by norm_num)

@[simp] theorem red_two : red (2 : ℚ) = 0 := by
  have h : (2 : ℚ) = 0 + 2 * ((1 : ℤ) : ℚ) := by norm_num
  rw [h, red_add_two_mul_int, red_zero]

theorem red_neg_red (a : ℚ) : red (-(red a)) = red (-a) := by
  have h : -(red a) = -a + 2 * ((⌊a / 2⌋ : ℤ) : ℚ) := by unfold red; ring
  rw [h, red_add_two_mul_int]

theorem red_eq_zero_iff (q : ℚ) : red q = 0 ↔ ∃ n : ℤ, 2 * (n : ℚ) = q := by
  constructor
  · intro h
    refine ⟨⌊q / 2⌋, ?_⟩
    unfold red at h
    linarith
  · rintro ⟨n, rfl⟩
    unfold red
    have h : (2 * (n : ℚ)) / 2 = (n : ℚ) := by ring
    rw [h, Int.floor_intCast]
    ring

/-- `q - red q` is an even integer. -/
theorem sub_red (q : ℚ) : ∃ n : ℤ, q = red q + 2 * (n : ℚ) :=
  ⟨⌊q / 2⌋, by unfold red; ring⟩

/-!
## Normalization of AlgPhase
-/

/- `=` on `AlgPhase` is strict: `ofRat 2 ≠ ofRat 0`.
    For phase equality we define `equiv`, for equality mod 2π -/
def normalize (p : AlgPhase) : AlgPhase := ofRat (red p.toRat)

/-- Equality of phases as angles. -/
def equiv (p q : AlgPhase) : Prop := normalize p = normalize q

instance (p q : AlgPhase) : Decidable (equiv p q) := inferInstanceAs (Decidable (_ = _))

theorem equiv_refl (p : AlgPhase) : equiv p p := rfl

theorem equiv_of_add_two (p : AlgPhase) (n : ℤ) :
    equiv (p + ofRat (2 * (n : ℚ))) p := by
  show ofRat (red _) = ofRat (red _)
  exact congrArg ofRat (red_add_two_mul_int p.toRat n)

@[simp] theorem normalize_idem (p : AlgPhase) : normalize (normalize p) = normalize p :=
  congrArg ofRat (red_idem p.toRat)
