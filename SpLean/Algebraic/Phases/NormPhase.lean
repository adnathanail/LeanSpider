import SpLean.Algebraic.Phases.Common

/-!
# Option C — `NormPhase`: a subtype pinned to the canonical window `[0, 2)`

Canonical representatives without any quotient machinery: `=` is exactly phase
equality, `DecidableEq` and `Repr` are trivial, and nothing is ever a
`Quotient.lift`.

The two costs, both visible below:

* `val : NormPhase → ℚ` is **not** additive (`(p + q).val = red (p.val + q.val)`),
  so `Function.Injective.addCommGroup` does not apply and every group law has to
  be proved by hand off `red_add_left` / `red_add_right`. More importantly the
  same failure hits `angle`: it is *definable* here, unlike in `CirclePhase`,
  but it is not a group hom — see `angle_not_additive`. So this option inherits
  option B's real problem (the semantics must route through `expI`) without
  inheriting its elegance.
* Every literal carries two proof terms, which is a problem for `reflectPhase`
  in `SpLean/Tactics.lean` — see the note at the bottom.
-/

namespace SpLean.Phases

/-- A phase `val·π` with `val` pinned to `[0, 2)`. -/
structure NormPhase where
  val : ℚ
  nonneg : 0 ≤ val
  lt_two : val < 2

namespace NormPhase

theorem ext' {p q : NormPhase} (h : p.val = q.val) : p = q := by
  cases p; cases q; subst h; rfl

instance : DecidableEq NormPhase := fun p q =>
  decidable_of_iff (p.val = q.val) ⟨fun h => ext' h, fun h => by rw [h]⟩

/-- The phase `q·π`, moved into the canonical window. -/
def ofRat (q : ℚ) : NormPhase := ⟨red q, red_nonneg q, red_lt_two q⟩

@[simp] theorem val_ofRat (q : ℚ) : (ofRat q).val = red q := rfl

@[simp] theorem ofRat_val (p : NormPhase) : ofRat p.val = p :=
  ext' (red_of_mem _ p.nonneg p.lt_two)

/-! ### The algebra, by hand

Note the shape of `val_add`: the constructor does the reducing, which is exactly
why `val` is not a hom and why none of Mathlib's transfer lemmas apply. -/

instance : Zero NormPhase := ⟨⟨0, le_rfl, by norm_num⟩⟩
instance : Add NormPhase := ⟨fun p q => ofRat (p.val + q.val)⟩
instance : Neg NormPhase := ⟨fun p => ofRat (-p.val)⟩

@[simp] theorem val_zero : (0 : NormPhase).val = 0 := rfl
@[simp] theorem val_add (p q : NormPhase) : (p + q).val = red (p.val + q.val) := rfl
@[simp] theorem val_neg (p : NormPhase) : (-p).val = red (-p.val) := rfl

@[simp] theorem ofRat_zero : ofRat (0 : ℚ) = 0 :=
  ext' (red_of_mem 0 le_rfl (by norm_num))

theorem ofRat_add (a b : ℚ) : ofRat (a + b) = ofRat a + ofRat b := by
  apply ext'
  simp only [val_ofRat, val_add]
  rw [red_add_left, red_add_right]

theorem ofRat_neg (a : ℚ) : ofRat (-a) = -ofRat a := by
  apply ext'
  simp only [val_ofRat, val_neg]
  rw [red_neg_red]

/-- Because `val` is not additive, Mathlib's `Function.Injective.addCommGroup`
transfer does not apply, and — unlike `RatPhase`, where every field came for
free — the `nsmul`/`zsmul` *defaults* don't work either: their `rfl` proof
obligations fail as soon as `add` normalises. Both have to be given explicitly. -/
instance : AddCommGroup NormPhase where
  add_assoc p q r := by
    apply ext'
    simp only [val_add]
    rw [red_add_left, red_add_right, add_assoc]
  zero_add p := by
    apply ext'
    simp only [val_add, val_zero, zero_add]
    exact red_of_mem _ p.nonneg p.lt_two
  add_zero p := by
    apply ext'
    simp only [val_add, val_zero, add_zero]
    exact red_of_mem _ p.nonneg p.lt_two
  neg_add_cancel p := by
    apply ext'
    simp only [val_add, val_neg, val_zero]
    rw [red_add_left, neg_add_cancel]
    exact red_of_mem 0 le_rfl (by norm_num)
  add_comm p q := by
    apply ext'
    simp only [val_add, add_comm]
  nsmul n p := ofRat ((n : ℚ) * p.val)
  nsmul_zero p := by
    apply ext'
    show red (((0 : ℕ) : ℚ) * p.val) = 0
    rw [Nat.cast_zero, zero_mul]
    exact red_of_mem 0 le_rfl (by norm_num)
  nsmul_succ n p := by
    apply ext'
    show red (((n + 1 : ℕ) : ℚ) * p.val) = red (red (((n : ℕ) : ℚ) * p.val) + p.val)
    rw [red_add_left]
    congr 1
    push_cast
    ring
  zsmul n p := ofRat ((n : ℚ) * p.val)
  zsmul_zero' p := by
    apply ext'
    show red (((0 : ℤ) : ℚ) * p.val) = 0
    rw [Int.cast_zero, zero_mul]
    exact red_of_mem 0 le_rfl (by norm_num)
  zsmul_succ' n p := by
    apply ext'
    show red (((Int.ofNat n.succ : ℤ) : ℚ) * p.val)
        = red (red (((Int.ofNat n : ℤ) : ℚ) * p.val) + p.val)
    rw [red_add_left]
    congr 1
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring
  zsmul_neg' n p := by
    apply ext'
    show red (((Int.negSucc n : ℤ) : ℚ) * p.val)
        = red (-(red ((((n.succ : ℕ) : ℤ) : ℚ) * p.val)))
    rw [red_neg_red]
    congr 1
    push_cast
    ring

@[simp] theorem ofRat_two : ofRat (2 : ℚ) = 0 := by
  apply ext'
  have h : (2 : ℚ) = 0 + 2 * ((1 : ℤ) : ℚ) := by norm_num
  simp only [val_ofRat, val_zero]
  rw [h, red_add_two_mul_int]
  exact red_of_mem 0 le_rfl (by norm_num)

/-! ### Display -/

def num (p : NormPhase) : ℤ := p.val.num
def den (p : NormPhase) : ℕ := p.val.den

/-- Like `CirclePhase`, always renders in `[0, 2π)`: `ofRat (-1/4)` shows
`7π/4`. The branch cut is baked into the type. -/
def format (p : NormPhase) : String := formatRat p.val

instance : Repr NormPhase := ⟨fun p _ => Std.Format.text p.format⟩
instance : ToString NormPhase := ⟨format⟩
instance : Inhabited NormPhase := ⟨0⟩

/-! ### Semantics: `angle` exists but is not a hom

This is the crux, and the reason this option is not a free lunch. `angle` is
definable (unlike in `CirclePhase`), but `angle_add` is false, so it cannot
carry the semantics any better than `CirclePhase.repAngle` can. -/

noncomputable def angle (p : NormPhase) : ℝ := (p.val : ℝ) * Real.pi

/-- The counterexample: `3π/2 + π` is `π/2` here, not `5π/2`. -/
theorem angle_not_additive : ∃ p q : NormPhase, (p + q).angle ≠ p.angle + q.angle := by
  refine ⟨ofRat (3 / 2), ofRat 1, ?_⟩
  have h32 : (ofRat (3 / 2 : ℚ)).val = 3 / 2 := red_of_mem _ (by norm_num) (by norm_num)
  have h1 : (ofRat (1 : ℚ)).val = 1 := red_of_mem _ (by norm_num) (by norm_num)
  have hsum : (ofRat (3 / 2 : ℚ) + ofRat 1).val = 1 / 2 := by
    rw [val_add, h32, h1]
    have h : (3 / 2 + 1 : ℚ) = 1 / 2 + 2 * ((1 : ℤ) : ℚ) := by norm_num
    rw [h, red_add_two_mul_int]
    exact red_of_mem _ (by norm_num) (by norm_num)
  simp only [angle, hsum, h32, h1]
  have hpi := Real.pi_pos
  push_cast
  intro h
  linarith

/-- `expI`, as everywhere, is the observation that does survive. -/
noncomputable def expI (p : NormPhase) : ℂ := expIRat p.val

@[simp] theorem expI_ofRat (q : ℚ) : (ofRat q).expI = expIRat q := expIRat_red q

theorem expI_add (p q : NormPhase) : (p + q).expI = p.expI * q.expI := by
  show expIRat (red (p.val + q.val)) = expIRat p.val * expIRat q.val
  rw [expIRat_red, expIRat_add]

/-! ### The reflection cost

`reflectPhase` (`SpLean/Tactics.lean`) builds an `Expr` for a phase from a
`MetaM` computation. For `RatPhase` that is a numerator and a denominator; here
it is a numerator, a denominator, **and two proof terms**, which have to be
closed terms rather than tactic blocks — so every reflected spider in every goal
carries a pair of `of_decide_eq_true` certificates. -/

example : NormPhase := ⟨1 / 2, by norm_num, by norm_num⟩

/-- And `decide` is not an escape hatch: `Rat.blt` does not reduce on an
unevaluated `1 / 2`, so

    example : NormPhase := ⟨1 / 2, by decide, by decide⟩

fails. `reflectPhase` would have to emit the `Rat.mk'` normal form together with
a certificate built by hand. -/
example : NormPhase := ⟨1 / 2, by norm_num, by norm_num⟩

end NormPhase

end SpLean.Phases
