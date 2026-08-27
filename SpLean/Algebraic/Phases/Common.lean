import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Shared plumbing for the three candidate phase representations

A phase is a *rational multiple of π*: the rational `q` denotes the angle `q·π`,
so `1/2` is `π/2` and the period is `q ↦ q + 2`.

All three candidates in this directory need the same two ingredients — a way to
pick a canonical representative modulo `2`, and the fact that `e^{iqπ}` doesn't
see that choice. The interesting question is *where each one puts them*:

* `RatPhase`  — nowhere in the type; `red` is called only by the `≈z` path.
* `CirclePhase` — inside a `Quotient.lift`, once per observation.
* `NormPhase` — inside the constructor, so every value is already reduced.
-/

namespace SpLean.Phases

/-- Canonical representative of `q` modulo `2`: the unique `r ∈ [0, 2)` with
`q - r ∈ 2ℤ`. -/
def red (q : ℚ) : ℚ := q - 2 * ⌊q / 2⌋

theorem red_nonneg (q : ℚ) : 0 ≤ red q := by
  have h : ((⌊q / 2⌋ : ℤ) : ℚ) ≤ q / 2 := Int.floor_le _
  unfold red
  linarith

theorem red_lt_two (q : ℚ) : red q < 2 := by
  have h : q / 2 < ((⌊q / 2⌋ : ℤ) : ℚ) + 1 := Int.lt_floor_add_one _
  unfold red
  linarith

/-- `red` is the identity on the canonical window `[0, 2)`. -/
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

/-- Reducing an operand first doesn't change the reduced sum. This one lemma is
what makes `NormPhase`'s addition associative and commutative. -/
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

/-! ## Display -/

/-- Human-readable form of the phase `q·π`: `0`, `π`, `-π`, `π/2`, `3π/2`, … -/
def formatRat (q : ℚ) : String :=
  if q.num = 0 then "0"
  else
    let ns := if q.num = 1 then "" else if q.num = -1 then "-" else toString q.num
    let ds := if q.den = 1 then "" else s!"/{q.den}"
    s!"{ns}π{ds}"

/-! ## The unit complex number a phase denotes

`e^{iqπ}` is the only thing about a phase that *all three* representations agree
on, because it is the only observation that is blind to the choice of
representative. -/

noncomputable def expIRat (q : ℚ) : ℂ :=
  Complex.exp ((q : ℂ) * (Real.pi : ℂ) * Complex.I)

theorem expIRat_add (a b : ℚ) : expIRat (a + b) = expIRat a * expIRat b := by
  unfold expIRat
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The key fact: reduction mod `2` is invisible to `e^{iqπ}`. -/
@[simp] theorem expIRat_red (q : ℚ) : expIRat (red q) = expIRat q := by
  have key : ((red q : ℚ) : ℂ) * (Real.pi : ℂ) * Complex.I
      = (q : ℂ) * (Real.pi : ℂ) * Complex.I
        - ((⌊q / 2⌋ : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    unfold red
    push_cast
    ring
  unfold expIRat
  rw [key, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

end SpLean.Phases
