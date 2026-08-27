import SemanticsTesting.Utils
import SemanticsTesting.«02Scalars»
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open SpLean.Algebraic

-- pqs ex 3.5
-- By combining the diagrams from 02Scalars,
--   find a ZX-diagram to represent the following scalar values z:

-- a) z = -1
abbrev scalarDiagNegOne := redPiCircleAnyGreen 1 ≫ redCircleTripleLinkGreenCircle
#zx scalarDiagNegOne
lemma scalar_univ_neg_one (f g : Wires 0) :
  scalarDiagNegOne.sem f g = -1 := by
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton]
  rw [scalar_sem_sqrt_two_e_i_alpha, scalar_sem_one_over_sqrt_two]
  push_cast
  unfold rootTwo eiTheta
  norm_num


-- b) z = e^{i θ} for any θ
abbrev scalarDiagEuler (θ : AlgPhase) := redPiCircleAnyGreen θ ≫ redCircleTripleLinkGreenCircle
#zx scalarDiagEuler
lemma scalar_univ_euler_form (θ : AlgPhase) (f g : Wires 0) :
    (scalarDiagEuler θ).sem f g = eiTheta θ.angle := by
  -- Composition of scalars is a sum over the unique element of `Wires 0`
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton,
    scalar_sem_sqrt_two_e_i_alpha, scalar_sem_one_over_sqrt_two]
  unfold rootTwo eiTheta
  field_simp

-- c) z = 1/2
abbrev scalarDiagHalf := redCircleTripleLinkGreenCircle ≫ redCircleTripleLinkGreenCircle
#zx scalarDiagHalf
lemma scalar_univ_half (f g : Wires 0) :
  scalarDiagHalf.sem f g = 1/2 := by
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton]
  rw [scalar_sem_one_over_sqrt_two, scalar_sem_one_over_sqrt_two]
  unfold rootTwo
  norm_cast
  ring_nf
  norm_num

-- d) z = cos θ for any value of θ
abbrev scalarDiagCosTheta (θ : AlgPhase) :=
  redPiCircleAnyGreen θ ≫
  redCircleTripleLinkGreenCircle ≫
  greenAlphaCircle (-2 • θ) ≫
  redCircleTripleLinkGreenCircle ≫
  redCircleTripleLinkGreenCircle
#zx scalarDiagCosTheta
lemma scalar_uni_cos_theta (θ : AlgPhase) (f g : Wires 0) :
    (scalarDiagCosTheta θ).sem f g = Complex.cos θ.angle := by
  -- Replace diagram semantics with scalars from previous lemmas
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton, scalar_sem_one_over_sqrt_two]
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton, scalar_sem_one_over_sqrt_two]
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton, scalar_sem_alpha]
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton, scalar_sem_one_over_sqrt_two, scalar_sem_sqrt_two_e_i_alpha]
  unfold rootTwo eiTheta
  -- Rewrite cos in terms of exp
  rw [Complex.cos]
  -- Shuffle expressions around
  nth_rw 4 [mul_right_comm]
  rw [mul_one_div_cancel]
  on_goal 2 => norm_num
  rw [one_mul, mul_add]
  -- e^x * e^y = e^{x + y}
  rw [← Complex.exp_add]
  -- Turn every `angle` into `π` times a rational, so `ring_nf` can normalise the
  -- exponents (`θ + -2θ = -θ`) instead of needing a hand-rolled lemma
  push_cast
  -- Normalise expressions
  ring_nf
  -- Deal with complex casting nastiness
  rw [show ((√2 : ℂ)⁻¹ ^ 2) = 1 / 2 by norm_cast ; simp]

-- TODO complete proof
--   our phases are rationals, so they cannot be used to construct ℝ and therefore ℂ

/-! ## Which scalars are reachable at all?

`Phase` is `num : ℤ` over `den : ℕ+`, so every phase is a *rational* multiple of
`π` and `e^{iα}` is always a root of unity. The `1/√2`s that Hadamard
contributes are not extra irrationality either: `ζ₈ + ζ₈⁻¹ = 2cos(π/4) = √2`, so
`1/√2 = (ζ₈ + ζ₈⁻¹)/2` is itself built from a root of unity and `1/2`.

Every diagram amplitude therefore lands in `ℤ[μ_∞, ½]` — the cyclotomic integers
with `2` inverted, a subring of `ℚᵃᵇ`. That set is countable, so a universality
statement quantified over all of `ℂ` would be false; this is the honest bound. -/

noncomputable def scalarRing : Subring ℂ :=
  Subring.closure ({(1/2 : ℂ)} ∪ {z | ∃ n : ℕ+, z ^ (n : ℕ) = 1})

lemma half_mem_scalarRing : (1/2 : ℂ) ∈ scalarRing :=
  Subring.subset_closure (Or.inl rfl)

lemma rootOfUnity_mem_scalarRing {z : ℂ} {n : ℕ+} (h : z ^ (n : ℕ) = 1) :
    z ∈ scalarRing :=
  Subring.subset_closure (Or.inr ⟨n, h⟩)

/-- `e^{iα}` for a `Phase` α is a `2·den`-th root of unity: the exponent becomes
`2πi·num`. -/
lemma phase_exp_pow (p : Phase) :
    (Complex.exp ((p.angle : ℝ) * Complex.I)) ^ (2 * (p.den : ℕ)) = 1 := by
  rw [← Complex.exp_nat_mul]
  have hden : ((p.den : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.den.ne_zero
  have h : ((2 * (p.den : ℕ) : ℕ) : ℂ) * ((p.angle : ℝ) * Complex.I)
      = (p.num : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    unfold Phase.angle
    push_cast
    field_simp
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

lemma phase_exp_mem_scalarRing (p : Phase) :
    Complex.exp ((p.angle : ℝ) * Complex.I) ∈ scalarRing :=
  rootOfUnity_mem_scalarRing (n := ⟨2 * (p.den : ℕ), by positivity⟩) (phase_exp_pow p)

/-- `ζ₈ + ζ₈⁻¹ = 2cos(π/4) = √2`, so `√2` is already cyclotomic. -/
lemma rootTwo_eq_zeta8_add_inv :
    Complex.exp (((⟨1, 4⟩ : Phase).angle : ℝ) * Complex.I)
      + Complex.exp (((⟨-1, 4⟩ : Phase).angle : ℝ) * Complex.I)
      = ((Real.sqrt 2 : ℝ) : ℂ) := by
  have h1 : ((⟨1, 4⟩ : Phase).angle : ℝ) = Real.pi / 4 := by
    unfold Phase.angle; norm_num; ring
  have h2 : ((⟨-1, 4⟩ : Phase).angle : ℝ) = -(Real.pi / 4) := by
    unfold Phase.angle; norm_num; ring
  rw [h1, h2, Complex.ofReal_neg, ← Complex.two_cos, ← Complex.ofReal_cos,
    Real.cos_pi_div_four]
  push_cast
  ring

lemma invRootTwo_mem_scalarRing : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ∈ scalarRing := by
  have hs : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  have h : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (1/2) * ((Real.sqrt 2 : ℝ) : ℂ) := by
    field_simp
    norm_cast
    rw [sq, hs]
  rw [h, ← rootTwo_eq_zeta8_add_inv]
  exact mul_mem half_mem_scalarRing
    (add_mem (phase_exp_mem_scalarRing _) (phase_exp_mem_scalarRing _))

lemma hadSem_mem_scalarRing (a b : Bool) : hadSem a b ∈ scalarRing := by
  unfold hadSem
  split
  · exact neg_mem invRootTwo_mem_scalarRing
  · exact invRootTwo_mem_scalarRing

lemma zSpiderSem_mem_scalarRing (p : Phase) {n m : ℕ} (f : Wires n) (g : Wires m) :
    zSpiderSem p.angle f g ∈ scalarRing := by
  unfold zSpiderSem
  refine add_mem ?_ (mul_mem (phase_exp_mem_scalarRing p) ?_) <;>
    · split
      exacts [one_mem _, zero_mem _]

lemma xSpiderSem_mem_scalarRing (p : Phase) {n m : ℕ} (f : Wires n) (g : Wires m) :
    xSpiderSem p.angle f g ∈ scalarRing := by
  unfold xSpiderSem
  refine Subring.sum_mem _ fun f' _ => Subring.sum_mem _ fun g' _ => ?_
  exact mul_mem
    (mul_mem (Subring.prod_mem _ fun i _ => hadSem_mem_scalarRing _ _)
      (zSpiderSem_mem_scalarRing p f' g'))
    (Subring.prod_mem _ fun j _ => hadSem_mem_scalarRing _ _)

/-- **Soundness bound.** Every amplitude of every algebraic ZX term lies in
`scalarRing`. In particular no scalar diagram can denote, say, `1/3` or `π`, so
universality can only ever be stated relative to this subring. -/
theorem sem_mem_scalarRing : ∀ {n m : ℕ} (d : ZX n m) (f : Wires n) (g : Wires m),
    d.sem f g ∈ scalarRing := by
  intro n m d
  induction d with
  | empty => intro f g; rw [ZX.sem]; exact one_mem _
  | wire =>
      intro f g
      rw [ZX.sem]
      split
      exacts [one_mem _, zero_mem _]
  | hadamard => intro f g; rw [ZX.sem]; exact hadSem_mem_scalarRing _ _
  | spider c n m φ =>
      intro f g
      cases c
      · exact zSpiderSem_mem_scalarRing φ f g
      · exact xSpiderSem_mem_scalarRing φ f g
  | stack a b iha ihb => intro f g; rw [ZX.sem]; exact mul_mem (iha _ _) (ihb _ _)
  | compose a b iha ihb =>
      intro f g
      rw [ZX.sem]
      exact Subring.sum_mem _ fun x _ => mul_mem (iha _ _) (ihb _ _)

/-! ## The converse: what *can* we build?

`2` is `greenCircle`, so all of `2^k` is reachable; `cos θ` gives a modulus in
`[-1, 1]`; `e^{iφ}` gives the argument. Together they cover every complex number
of the form `2^k · cos(aπ) · e^{ibπ}` with `a, b` rational. -/

/-- `2^k`, as `k` copies of `greenCircle` composed together. -/
def scalarDiagTwoPow : ℕ → ZX 0 0
  | 0 => ZX.empty
  | k + 1 => greenCircle ≫ scalarDiagTwoPow k

lemma scalar_univ_two_pow (k : ℕ) :
    ∀ f g : Wires 0, (scalarDiagTwoPow k).sem f g = 2 ^ k := by
  induction k with
  | zero => intro f g; rw [scalarDiagTwoPow, ZX.sem]; norm_num
  | succ k ih =>
      intro f g
      rw [scalarDiagTwoPow, ZX.sem, Finset.univ_unique, Finset.sum_singleton,
        scalar_sem_two, ih]
      ring

/-- Polar form: modulus `2^k · cos θ`, argument `φ`. -/
abbrev scalarDiagPolar (k : ℕ) (θ φ : Phase) : ZX 0 0 :=
  scalarDiagTwoPow k ≫ scalarDiagCosTheta θ ≫ scalarDiagEuler φ

lemma scalar_univ_polar (k : ℕ) (θ φ : Phase) (f g : Wires 0) :
    (scalarDiagPolar k θ φ).sem f g
      = 2 ^ k * Complex.cos θ.angle * Complex.exp (φ.angle * Complex.I) := by
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton, scalar_univ_euler_form]
  rw [ZX.sem, Finset.univ_unique, Finset.sum_singleton, scalar_univ_two_pow,
    scalar_uni_cos_theta]

/-! ## Density

The construction above is exact but countable, so it cannot hit every complex
number. It does however hit a *dense* set: `2^k` covers every scale, `cos` of a
rational multiple of `π` covers `[-1, 1]` densely, and `e^{ibπ}` covers the
circle densely. This is the best converse the rational `Phase` allows, and it is
the usual "approximate universality" statement. -/

/-- The scalars some diagram actually denotes. -/
def Constructible : Set ℂ := {z : ℂ | ∃ d : ZX 0 0, ∀ f g : Wires 0, d.sem f g = z}

/-- A `Phase` is `num/den`, so its angle is `q·π` for a rational `q` — and every
rational arises this way. Hence phase angles are dense in `ℝ`. -/
lemma dense_phase_angle : Dense {x : ℝ | ∃ p : Phase, p.angle = x} := by
  have hrange : DenseRange (fun q : ℚ => (q : ℝ) * Real.pi) :=
    DenseRange.comp ((Homeomorph.mulRight₀ Real.pi Real.pi_ne_zero).surjective.denseRange)
      Rat.denseRange_cast (by fun_prop)
  refine Dense.mono ?_ hrange
  rintro x ⟨q, rfl⟩
  exact ⟨⟨q.num, ⟨q.den, q.den_pos⟩⟩, by simp [Phase.angle, Rat.cast_def]⟩

/-- `scalarDiagPolar` read as a continuous map of its two angles. -/
noncomputable def polarMap (k : ℕ) (p : ℝ × ℝ) : ℂ :=
  ((2 ^ k * Real.cos p.1 : ℝ) : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)

lemma continuous_polarMap (k : ℕ) : Continuous (polarMap k) := by
  unfold polarMap; fun_prop

/-- Rational angles land in `Constructible`, by `scalar_univ_polar`. -/
lemma polarMap_image_subset (k : ℕ) :
    polarMap k '' ({x : ℝ | ∃ p : Phase, p.angle = x} ×ˢ {x : ℝ | ∃ p : Phase, p.angle = x})
      ⊆ Constructible := by
  rintro z ⟨⟨a, b⟩, ⟨⟨θ, rfl⟩, ⟨φ, rfl⟩⟩, rfl⟩
  refine ⟨scalarDiagPolar k θ φ, fun f g => ?_⟩
  rw [scalar_univ_polar]
  simp only [polarMap, Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_pow,
    Complex.ofReal_ofNat]

/-- **Approximate universality for scalars.** Every complex number is a limit of
diagram amplitudes. -/
theorem dense_constructible : Dense Constructible := by
  intro w
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖w‖ (by norm_num : (1:ℝ) < 2)
  have hpos : (0:ℝ) < 2 ^ k := by positivity
  have hle : ‖w‖ / 2 ^ k ≤ 1 := (div_le_one hpos).mpr hk.le
  have hge : (-1:ℝ) ≤ ‖w‖ / 2 ^ k := by
    have : (0:ℝ) ≤ ‖w‖ / 2 ^ k := by positivity
    linarith
  have hw : w = polarMap k (Real.arccos (‖w‖ / 2 ^ k), Complex.arg w) := by
    have h2 : (2:ℝ) ^ k * (‖w‖ / 2 ^ k) = ‖w‖ := by field_simp
    simp only [polarMap, Real.cos_arccos hge hle, h2]
    exact (Complex.norm_mul_exp_arg_mul_I w).symm
  rw [hw]
  exact closure_mono (polarMap_image_subset k)
    (image_closure_subset_closure_image (continuous_polarMap k)
      ⟨_, (dense_phase_angle.prod dense_phase_angle) _, rfl⟩)
