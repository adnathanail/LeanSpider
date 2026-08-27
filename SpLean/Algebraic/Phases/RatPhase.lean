import SpLean.Algebraic.Phases.Common

/-!
# Option A — `RatPhase`: an opaque wrapper around `ℚ`, *not* normalised

The phase `q` denotes the angle `q·π`. Two phases that differ by `2` are
different *values* (`RatPhase.ofRat 2 ≠ 0`) but denote the same angle; the
2π-normalisation lives in `RatPhase.equiv`, which is the only place `≈z` needs
it.

`def` rather than `abbrev` is deliberate: `inferInstanceAs` hands over exactly
the `AddCommGroup` structure and nothing else, so `+`, `-`, `0` and `ℤ`-smul all
come from Mathlib while `*` and `/` — which are meaningless on an angle — do not
typecheck.
-/

namespace SpLean.Phases

def RatPhase : Type := ℚ

namespace RatPhase

instance : AddCommGroup RatPhase := inferInstanceAs (AddCommGroup ℚ)
instance : DecidableEq RatPhase := inferInstanceAs (DecidableEq ℚ)
instance : Inhabited RatPhase := inferInstanceAs (Inhabited ℚ)

/-- The phase `q·π`. -/
def ofRat (q : ℚ) : RatPhase := q

/-- The rational multiple of π that this phase is. -/
def toRat (p : RatPhase) : ℚ := p

@[simp] theorem toRat_ofRat (q : ℚ) : (ofRat q).toRat = q := rfl
@[simp] theorem ofRat_toRat (p : RatPhase) : ofRat p.toRat = p := rfl

theorem ext {p q : RatPhase} (h : p.toRat = q.toRat) : p = q := h

/-! ### The whole algebra is inherited, and every law is `rfl` -/

@[simp] theorem toRat_zero : (0 : RatPhase).toRat = 0 := rfl
@[simp] theorem toRat_add (p q : RatPhase) : (p + q).toRat = p.toRat + q.toRat := rfl
@[simp] theorem toRat_neg (p : RatPhase) : (-p).toRat = -p.toRat := rfl
@[simp] theorem toRat_sub (p q : RatPhase) : (p - q).toRat = p.toRat - q.toRat := rfl

@[simp] theorem toRat_zsmul (n : ℤ) (p : RatPhase) : (n • p).toRat = (n : ℚ) * p.toRat := by
  show n • p.toRat = (n : ℚ) * p.toRat
  exact zsmul_eq_mul _ _

@[simp] theorem ofRat_add (a b : ℚ) : ofRat (a + b) = ofRat a + ofRat b := rfl

/-! ### Display -/

def num (p : RatPhase) : ℤ := p.toRat.num
def den (p : RatPhase) : ℕ := p.toRat.den

/-- Renders the phase *as written*: `ofRat (-1/4)` shows `-π/4`, `ofRat (5/2)`
shows `5π/2`. Nothing has silently moved it into `[0, 2π)`. -/
def format (p : RatPhase) : String := formatRat p.toRat

instance : Repr RatPhase := ⟨fun p _ => Std.Format.text p.format⟩
instance : ToString RatPhase := ⟨format⟩

/-! ### 2π-normalisation, quarantined

`=` on `RatPhase` is strict: `ofRat 2 ≠ ofRat 0`. Phase equality — the thing
`ZXDiagram`'s `BEq` and `≈z` actually want — is `equiv`, and it is the *only*
place `red` gets called. Note that `=` stays a lawful, decidable equality, so
nothing else in the development has to worry about a `BEq` that disagrees with
it. -/

def normalize (p : RatPhase) : RatPhase := ofRat (red p.toRat)

/-- Equality of phases as angles. -/
def equiv (p q : RatPhase) : Prop := normalize p = normalize q

instance (p q : RatPhase) : Decidable (equiv p q) := inferInstanceAs (Decidable (_ = _))

theorem equiv_refl (p : RatPhase) : equiv p p := rfl

theorem equiv_of_add_two (p : RatPhase) (n : ℤ) :
    equiv (p + ofRat (2 * (n : ℚ))) p := by
  show ofRat (red _) = ofRat (red _)
  exact congrArg ofRat (red_add_two_mul_int p.toRat n)

@[simp] theorem normalize_idem (p : RatPhase) : normalize (normalize p) = normalize p :=
  congrArg ofRat (red_idem p.toRat)

/-! ### Semantics: `angle` is an honest group hom into `ℝ`

This is the property the other two representations cannot have, and it is what
makes every phase lemma in the semantics a `push_cast; ring`. -/

noncomputable def angle (p : RatPhase) : ℝ := (p.toRat : ℝ) * Real.pi

@[simp] theorem angle_add (p q : RatPhase) : (p + q).angle = p.angle + q.angle := by
  unfold angle
  rw [toRat_add]
  push_cast
  ring

@[simp] theorem angle_neg (p : RatPhase) : (-p).angle = -p.angle := by
  unfold angle
  rw [toRat_neg]
  push_cast
  ring

@[simp] theorem angle_zero : (0 : RatPhase).angle = 0 := by
  unfold angle
  rw [toRat_zero]
  push_cast
  ring

theorem angle_zsmul (n : ℤ) (p : RatPhase) : (n • p).angle = (n : ℝ) * p.angle := by
  unfold angle
  rw [toRat_zsmul]
  push_cast
  ring

noncomputable def expI (p : RatPhase) : ℂ := expIRat p.toRat

theorem expI_add (p q : RatPhase) : (p + q).expI = p.expI * q.expI :=
  expIRat_add _ _

/-- `equiv` is exactly the kernel of the denotation, as it should be. -/
theorem expI_normalize (p : RatPhase) : (normalize p).expI = p.expI :=
  expIRat_red p.toRat

theorem expI_congr {p q : RatPhase} (h : equiv p q) : p.expI = q.expI := by
  rw [← expI_normalize p, ← expI_normalize q, h]

end RatPhase

end SpLean.Phases
