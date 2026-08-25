import SpLean.Algebraic.ZX
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Denotational semantics for algebraic ZX terms

A `ZX n m` term denotes a tensor: a complex amplitude for every assignment of
Booleans to its `n` input wires and `m` output wires,
`⟦d⟧ : (Fin n → Bool) → (Fin m → Bool) → ℂ`.

This "matrix as a function of boundary bit-vectors" presentation is chosen over
`Matrix (Fin (2^m)) (Fin (2^n)) ℂ` deliberately: `stack` splits a boundary
assignment with `Fin.castAdd`/`Fin.natAdd` instead of reindexing along
`2^(n+p) = 2^n * 2^p`, so no power-of-two casts ever appear. It is also the
tensor-network view of a diagram, which is the right vocabulary for the planned
hypergraph-isomorphism work: permuting wires is reindexing a sum, i.e. an
`Equiv`, not a matrix conjugation.

Equivalence (`≈zx`) is semantic equality up to a nonzero global scalar, as in
VyZX — ZX rules such as the bialgebra and copy rules only hold up to scalar,
and the syntax has no scalar constructor to track them with. Rules that are
scalar-exact (spider fusion, identity removal) are proved here with scalar `1`.
-/

noncomputable section

/-- The angle in radians denoted by a `Phase`, i.e. `num/den · π`. -/
def Phase.angle (p : Phase) : ℝ :=
  (p.num : ℝ) / ((p.den : ℕ) : ℝ) * Real.pi

theorem Phase.angle_add (p q : Phase) : (p + q).angle = p.angle + q.angle := by
  have hp : ((p.den : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.den.pos.ne'
  have hq : ((q.den : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den.pos.ne'
  show Phase.angle (Phase.add p q) = _
  unfold Phase.angle Phase.add
  push_cast [PNat.mul_coe]
  rw [← add_mul, div_add_div _ _ hp hq]
  ring

theorem Phase.angle_neg (p : Phase) : (-p).angle = -p.angle := by
  show Phase.angle (Phase.neg p) = _
  unfold Phase.angle Phase.neg
  push_cast
  ring

@[simp] theorem Phase.angle_zero : (⟨0, 1⟩ : Phase).angle = 0 := by
  simp [Phase.angle]

namespace SpLean.Algebraic

open Complex (I)

/-- A boundary assignment: one Boolean per open wire. -/
abbrev Wires (n : ℕ) := Fin n → Bool

/-- Tensor of a Z spider: `1` on the all-`false` boundary, `e^{iα}` on the
all-`true` boundary, `0` elsewhere. When `n = m = 0` both indicators fire and
the scalar is `1 + e^{iα}`, as it should be. -/
def zSpiderSem (α : ℝ) {n m : ℕ} (f : Wires n) (g : Wires m) : ℂ :=
  (if (∀ i, f i = false) ∧ (∀ j, g j = false) then 1 else 0)
    + Complex.exp (α * I) *
        (if (∀ i, f i = true) ∧ (∀ j, g j = true) then 1 else 0)

/-- One matrix entry of the Hadamard gate. -/
def hadSem (a b : Bool) : ℂ :=
  if a && b then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- Tensor of an X spider: a Z spider conjugated by Hadamards on every wire. -/
def xSpiderSem (α : ℝ) {n m : ℕ} (f : Wires n) (g : Wires m) : ℂ :=
  ∑ f' : Wires n, ∑ g' : Wires m,
    (∏ i, hadSem (f i) (f' i)) * zSpiderSem α f' g' * (∏ j, hadSem (g' j) (g j))

/-- Denotation of an algebraic ZX term as a boundary tensor.
`compose` sums over the shared internal boundary; `stack` splits the boundary
assignment between the two halves. -/
def ZX.sem : {n m : ℕ} → ZX n m → Wires n → Wires m → ℂ
  | _, _, .empty, _, _ => 1                                  -- Empty diagram = 1
  | _, _, .wire, f, g => if f 0 = g 0 then 1 else 0          -- Wire = identity matrix
  | _, _, .hadamard, f, g => hadSem (f 0) (g 0)
  | _, _, .spider .Z _ _ φ, f, g => zSpiderSem φ.angle f g
  | _, _, .spider .X _ _ φ, f, g => xSpiderSem φ.angle f g
  | _, _, .compose a b, f, h => ∑ g, a.sem f g * b.sem g h   -- Composition = tensor contraction
  | _, _, .stack a b, f, g =>
      -- Split up the responsibility for wire indexes across the two stacked diagrams
      a.sem (fun i => f (Fin.castAdd _ i)) (fun j => g (Fin.castAdd _ j)) *
        b.sem (fun i => f (Fin.natAdd _ i)) (fun j => g (Fin.natAdd _ j))

/-- Semantic equivalence of ZX terms: equal tensors up to a nonzero global
scalar (VyZX's proportionality). -/
def ZX.Equiv {n m : ℕ} (a b : ZX n m) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ∀ f g, a.sem f g = c * b.sem f g

@[inherit_doc] scoped infix:50 " ≈zx " => ZX.Equiv

namespace ZX.Equiv

theorem refl {n m : ℕ} (a : ZX n m) : a ≈zx a :=
  ⟨1, one_ne_zero, fun _ _ => (one_mul _).symm⟩

theorem symm {n m : ℕ} {a b : ZX n m} : a ≈zx b → b ≈zx a
  | ⟨c, hc, h⟩ => ⟨c⁻¹, inv_ne_zero hc, fun f g => by rw [h f g, inv_mul_cancel_left₀ hc]⟩

theorem trans {n m : ℕ} {a b c : ZX n m} : a ≈zx b → b ≈zx c → a ≈zx c
  | ⟨c₁, hc₁, h₁⟩, ⟨c₂, hc₂, h₂⟩ =>
    ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, fun f g => by rw [h₁ f g, h₂ f g, mul_assoc]⟩

instance {n m : ℕ} :
    Trans (ZX.Equiv (n := n) (m := m)) (ZX.Equiv (n := n) (m := m))
      (ZX.Equiv (n := n) (m := m)) :=
  ⟨trans⟩

/-- `compose` respects `≈zx` (scalars multiply). -/
theorem compose_congr {n m k : ℕ} {a a' : ZX n m} {b b' : ZX m k}
    (ha : a ≈zx a') (hb : b ≈zx b') : (a ≫ b) ≈zx (a' ≫ b') := by
  obtain ⟨c₁, hc₁, h₁⟩ := ha
  obtain ⟨c₂, hc₂, h₂⟩ := hb
  refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, fun f h => ?_⟩
  simp only [ZX.sem, h₁, h₂, Finset.mul_sum]
  exact Finset.sum_congr rfl fun g _ => by ring

/-- `stack` respects `≈zx` (scalars multiply). -/
theorem stack_congr {n m p q : ℕ} {a a' : ZX n m} {b b' : ZX p q}
    (ha : a ≈zx a') (hb : b ≈zx b') : (a ⊗ b) ≈zx (a' ⊗ b') := by
  obtain ⟨c₁, hc₁, h₁⟩ := ha
  obtain ⟨c₂, hc₂, h₂⟩ := hb
  refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, fun f g => ?_⟩
  simp only [ZX.sem, h₁, h₂]
  ring

end ZX.Equiv

theorem ZX.equivalence (n m : ℕ) : Equivalence (ZX.Equiv (n := n) (m := m)) :=
  ⟨ZX.Equiv.refl, ZX.Equiv.symm, ZX.Equiv.trans⟩

/-- Transport a term along index equalities. Needed because e.g. `(a ⊗ b) ⊗ c`
and `a ⊗ (b ⊗ c)` have propositionally but not definitionally equal indices. -/
def ZX.cast {n m n' m' : ℕ} (hn : n = n') (hm : m = m') (a : ZX n m) : ZX n' m' :=
  hn ▸ hm ▸ a

@[simp] theorem ZX.sem_cast {n m n' m' : ℕ} (hn : n = n') (hm : m = m') (a : ZX n m)
    (f : Wires n') (g : Wires m') :
    (a.cast hn hm).sem f g
      = a.sem (fun i => f (Fin.cast hn i)) (fun j => g (Fin.cast hm j)) := by
  subst hn; subst hm; rfl

/-! ## Sums over small boundaries -/

/-- `Wires 1` is just a single Boolean. -/
def boolWireEquiv : Bool ≃ Wires 1 where
  toFun b _ := b
  invFun g := g 0
  left_inv _ := rfl
  right_inv g := funext fun i => by rw [Subsingleton.elim i 0]

theorem sum_wires_one (F : Wires 1 → ℂ) :
    ∑ g : Wires 1, F g = F (fun _ => true) + F (fun _ => false) := by
  rw [← Equiv.sum_comp boolWireEquiv F, Fintype.sum_bool]
  rfl

/-! ## Proved rules -/

/-- Spider fusion (single connecting wire): two Z spiders joined by a wire
merge, adding phases. Scalar-exact. -/
theorem zSpider_fusion (n m : ℕ) (α β : Phase) :
    (ZX.spider .Z n 1 α ≫ ZX.spider .Z 1 m β) ≈zx ZX.spider .Z n m (α + β) := by
  refine ⟨1, one_ne_zero, fun f h => ?_⟩
  rw [one_mul]
  simp only [ZX.sem]
  rw [sum_wires_one]
  simp [zSpiderSem, Phase.angle_add, add_mul, Complex.exp_add, ite_and]
  split_ifs <;> ring

/-- Full spider fusion: two Z spiders joined by any positive number of wires
merge, adding phases. The sum over the shared boundary collapses to its
all-`false` and all-`true` assignments; every mixed assignment contributes `0`. -/
theorem zSpider_fusion_full (n m k : ℕ) (α β : Phase) :
    (ZX.spider .Z n (k + 1) α ≫ ZX.spider .Z (k + 1) m β) ≈zx
      ZX.spider .Z n m (α + β) := by
  refine ⟨1, one_ne_zero, fun f h => ?_⟩
  rw [one_mul]
  simp only [ZX.sem]
  have key : ∀ g : Wires (k + 1),
      zSpiderSem α.angle f g * zSpiderSem β.angle g h =
        (if g = (fun _ => false) then
            (if (∀ i, f i = false) ∧ (∀ j, h j = false) then 1 else 0) else 0)
          + (if g = (fun _ => true) then
              Complex.exp (α.angle * I) * Complex.exp (β.angle * I) *
                (if (∀ i, f i = true) ∧ (∀ j, h j = true) then 1 else 0) else 0) := by
    intro g
    by_cases hgf : g = fun _ => false
    · subst hgf
      simp [zSpiderSem, ite_and, funext_iff]
      split_ifs <;> rfl
    · by_cases hgt : g = fun _ => true
      · subst hgt
        simp [zSpiderSem, ite_and, funext_iff]
        split_ifs <;> rfl
      · have h1 : ¬ ∀ x, g x = false := fun H => hgf (funext H)
        have h2 : ¬ ∀ x, g x = true := fun H => hgt (funext H)
        simp [zSpiderSem, hgf, hgt, h1, h2]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [zSpiderSem, Phase.angle_add, add_mul, Complex.exp_add, ite_and]

/-- Identity: a bare wire is a phaseless Z spider. -/
theorem wire_equiv_zSpider : ZX.wire ≈zx ZX.spider .Z 1 1 ⟨0, 1⟩ := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, zSpiderSem, Fin.forall_fin_one, Phase.angle_zero]
  cases f 0 <;> cases g 0 <;> simp

/-- Phases are angles: `2π` is the same as `0`. -/
theorem zSpider_two_pi (n m : ℕ) :
    ZX.spider .Z n m ⟨2, 1⟩ ≈zx ZX.spider .Z n m ⟨0, 1⟩ := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  have h2 : ((⟨2, 1⟩ : Phase).angle : ℂ) * I = 2 * Real.pi * I := by
    norm_num [Phase.angle]
  simp only [ZX.sem, zSpiderSem, h2, Complex.exp_two_pi_mul_I, Phase.angle_zero,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero]

/-- Opposite phases cancel: `α + (-α)` is the phaseless spider. -/
theorem zSpider_phase_cancel (n m : ℕ) (α : Phase) :
    ZX.spider .Z n m (α + -α) ≈zx ZX.spider .Z n m ⟨0, 1⟩ := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, zSpiderSem, Phase.angle_add, Phase.angle_neg, add_neg_cancel,
    Phase.angle_zero]

/-- Two Hadamards cancel to a wire. Scalar-exact. -/
theorem hadamard_hadamard : (ZX.hadamard ≫ ZX.hadamard) ≈zx ZX.wire := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem]
  rw [sum_wires_one]
  have key : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  cases f 0 <;> cases g 0 <;>
    simp [hadSem, mul_neg, neg_mul, key] <;> norm_num

/-- Sequential composition is associative on the nose (indices already agree). -/
theorem compose_assoc {n m k l : ℕ} (a : ZX n m) (b : ZX m k) (c : ZX k l) :
    ((a ≫ b) ≫ c) ≈zx (a ≫ (b ≫ c)) := by
  refine ⟨1, one_ne_zero, fun f h => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun g₁ _ => Finset.sum_congr rfl fun g₂ _ => by ring

/-- Stacking is associative up to `cast`: the indices `(n₁ + n₂) + n₃` and
`n₁ + (n₂ + n₃)` are only propositionally equal, which is exactly the
rebracketing friction the planned hypergraph-isomorphism layer removes. -/
theorem stack_assoc {n₁ m₁ n₂ m₂ n₃ m₃ : ℕ}
    (a : ZX n₁ m₁) (b : ZX n₂ m₂) (c : ZX n₃ m₃) :
    (((a ⊗ b) ⊗ c).cast (Nat.add_assoc n₁ n₂ n₃) (Nat.add_assoc m₁ m₂ m₃)) ≈zx
      (a ⊗ (b ⊗ c)) := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, ZX.sem_cast, mul_assoc]
  refine congrArg₂ (· * ·) ?_ (congrArg₂ (· * ·) ?_ ?_) <;>
    exact congrArg₂ _
      (funext fun i => congrArg f (Fin.ext (by simp [Nat.add_assoc])))
      (funext fun j => congrArg g (Fin.ext (by simp [Nat.add_assoc])))

/-- Chained fusions via `calc`, using the congruence lemma to rewrite in a
subterm — the shape a future `zx_rw` tactic automates. -/
example (n m : ℕ) (α β γ : Phase) :
    ((ZX.spider .Z n 1 α ≫ ZX.spider .Z 1 1 β) ≫ ZX.spider .Z 1 m γ) ≈zx
      ZX.spider .Z n m (α + β + γ) :=
  calc ((ZX.spider .Z n 1 α ≫ ZX.spider .Z 1 1 β) ≫ ZX.spider .Z 1 m γ)
      ≈zx (ZX.spider .Z n 1 (α + β) ≫ ZX.spider .Z 1 m γ) :=
        ZX.Equiv.compose_congr (zSpider_fusion n 1 α β) (ZX.Equiv.refl _)
    _ ≈zx ZX.spider .Z n m (α + β + γ) := zSpider_fusion n m (α + β) γ

end SpLean.Algebraic
