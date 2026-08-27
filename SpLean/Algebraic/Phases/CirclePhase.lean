import SpLean.Algebraic.Phases.Common
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Option B — `CirclePhase`: the honest quotient `ℚ ⧸ 2ℤ`

`AddCircle p` is an `abbrev` for `𝕜 ⧸ zmultiples p`, so `AddCircle (2 : ℚ)`
*is* `ℚ ⧸ 2ℤ` — the two names in the discussion were the same option all along.
The Mathlib precedent one level up is `Real.Angle := AddCircle (2 * π)`.

Here `=` is exactly phase equality: `ofRat 2 = 0` on the nose, `DecidableEq`
agrees with it, and there is no lawless `BEq` anywhere. The price is collected
below, in three instalments:

1. Every observation (`rep`, `format`, `num`, `den`) is a `Quotient.lift`
   carrying a proof that it doesn't see the representative.
2. `angle : CirclePhase → ℝ` **cannot be defined at all** — see the comment
   below. Only `expI` survives, so the semantics has to be rewritten to take a
   unit complex number instead of a real angle.
3. Every proof about a phase starts with `Quotient.inductionOn`.

Note also that Mathlib's own canonical-representative machinery for `AddCircle`
(`AddCircle.equivIco`, via `toIcoDiv`) is defined with `Exists.choose` and is
therefore **noncomputable**. To get anything to `#eval` you have to supply your
own computable reduction and prove it lands in `[0, 2)` — which is to say, you
end up writing `NormPhase` and then wrapping it in a quotient.
-/

namespace SpLean.Phases

def CirclePhase : Type := AddCircle (2 : ℚ)

namespace CirclePhase

instance : AddCommGroup CirclePhase := inferInstanceAs (AddCommGroup (AddCircle (2 : ℚ)))

/-- The phase `q·π`. -/
def ofRat (q : ℚ) : CirclePhase := ((q : AddCircle (2 : ℚ)) : CirclePhase)

instance : Inhabited CirclePhase := ⟨0⟩

/-! ### The coercion is a hom definitionally -/

@[simp] theorem ofRat_add (a b : ℚ) : ofRat (a + b) = ofRat a + ofRat b := rfl
@[simp] theorem ofRat_neg (a : ℚ) : ofRat (-a) = -ofRat a := rfl
@[simp] theorem ofRat_sub (a b : ℚ) : ofRat (a - b) = ofRat a - ofRat b := rfl
@[simp] theorem ofRat_zero : ofRat 0 = 0 := rfl

/-- The period really is `2`: this is the one thing `RatPhase` cannot say. -/
@[simp] theorem ofRat_two : ofRat 2 = 0 := AddCircle.coe_period (2 : ℚ)

theorem ofRat_eq_zero_iff (q : ℚ) : ofRat q = 0 ↔ ∃ n : ℤ, 2 * (n : ℚ) = q := by
  show ((q : AddCircle (2 : ℚ)) = 0) ↔ _
  rw [AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← hn, zsmul_eq_mul]; ring⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← hn, zsmul_eq_mul]; ring⟩

theorem ofRat_eq_iff (a b : ℚ) : ofRat a = ofRat b ↔ ∃ n : ℤ, b = a + 2 * (n : ℚ) := by
  rw [← sub_eq_zero, ← ofRat_sub, ofRat_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨-n, by push_cast; linarith⟩
  · rintro ⟨n, hn⟩; exact ⟨-n, by push_cast; linarith⟩

/-! ### Instalment 1: every observation is a lift

`rep` is the only way out of the quotient, and it costs a proof. Everything
below — `format`, `num`, `den`, `Repr` — has to go through it. -/

/-- The canonical representative in `[0, 2)`. -/
def rep : CirclePhase → ℚ :=
  Quotient.lift red fun a b h => by
    obtain ⟨n, hn⟩ := (ofRat_eq_iff a b).mp (Quotient.sound h)
    rw [hn, red_add_two_mul_int]

@[simp] theorem rep_ofRat (q : ℚ) : (ofRat q).rep = red q := rfl

theorem rep_nonneg (x : CirclePhase) : 0 ≤ x.rep :=
  Quotient.inductionOn x fun a => red_nonneg a

theorem rep_lt_two (x : CirclePhase) : x.rep < 2 :=
  Quotient.inductionOn x fun a => red_lt_two a

@[simp] theorem ofRat_rep (x : CirclePhase) : ofRat x.rep = x :=
  Quotient.inductionOn x fun a => by
    -- even getting back to your own API needs a `show`: the induction hands you
    -- `⟦a⟧`, not `ofRat a`
    show ofRat (ofRat a).rep = ofRat a
    rw [rep_ofRat, ofRat_eq_iff]
    exact sub_red a

/-- Decidable equality has to be routed through `rep` — there is no structural
equality to derive. -/
instance : DecidableEq CirclePhase := fun x y =>
  decidable_of_iff (x.rep = y.rep) <| by
    constructor
    · intro h; rw [← ofRat_rep x, ← ofRat_rep y, h]
    · intro h; rw [h]

def num (x : CirclePhase) : ℤ := x.rep.num
def den (x : CirclePhase) : ℕ := x.rep.den

/-- Always renders in `[0, 2π)`: `ofRat (-1/4)` comes out as `7π/4`, and there
is no way to ask for the phase "as written" because that information is gone. -/
def format (x : CirclePhase) : String := formatRat x.rep

instance : Repr CirclePhase := ⟨fun x _ => Std.Format.text x.format⟩
instance : ToString CirclePhase := ⟨format⟩

/-! ### Instalment 2: `angle` does not exist

    def angle (x : CirclePhase) : ℝ := Quotient.lift (fun q => (q : ℝ) * Real.pi) ??? x

is unprovable: `ofRat 0 = ofRat 2` but `0 * π ≠ 2 * π`. The best you can do is
take the angle *of the canonical representative*, and that is not additive —
see `repAngle_add_ne` below. So `zSpiderSem (α : ℝ)` and `xSpiderSem (α : ℝ)`
have to be reformulated in terms of `expI`, and every
`simp only [..., Phase.angle]` in `SemanticsTesting/` has to become a lemma
about exponentials. -/

/-- The angle of the canonical representative — lands in `[0, 2π)`, but is
**not** a group hom. -/
noncomputable def repAngle (x : CirclePhase) : ℝ := (x.rep : ℝ) * Real.pi

/-- `expI` is well defined precisely because it cannot see the representative;
this is the only observation of a phase that survives quotienting. -/
noncomputable def expI (x : CirclePhase) : ℂ := expIRat x.rep

@[simp] theorem expI_ofRat (q : ℚ) : (ofRat q).expI = expIRat q := by
  rw [expI, rep_ofRat, expIRat_red]

/-! ### Instalment 3: proofs start with `Quotient.inductionOn` -/

theorem expI_add (x y : CirclePhase) : (x + y).expI = x.expI * y.expI := by
  induction x using Quotient.inductionOn with | _ a =>
  induction y using Quotient.inductionOn with | _ b =>
  show (ofRat a + ofRat b).expI = (ofRat a).expI * (ofRat b).expI
  rw [← ofRat_add, expI_ofRat, expI_ofRat, expI_ofRat, expIRat_add]

/-- What you buy: `2π = 0` is definitional rather than a semantic theorem. -/
theorem ofRat_add_two (q : ℚ) : ofRat (q + 2) = ofRat q := by
  rw [ofRat_add, ofRat_two, add_zero]

end CirclePhase

end SpLean.Phases
