import SpLean.Hypergraph.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Fin

/-!
# Denotation of a hypergraph

A wire carries one bit, so an assignment is `Fin H.wires → Bool`. Each box
contributes its tensor applied to the bits on its legs, the boundary is pinned
by `f` and `g`, identified wires are forced equal, and everything else is
summed over.

Every tensor here is invariant under permuting its legs, which is what makes
the encoding sound: a spider is `1` when all its legs are `false`, `expI φ`
when all are `true`, and `0` otherwise, and it does not distinguish inputs from
outputs. That is exactly `zSpiderSem` in `SpLean/Algebraic/Semantics.lean` read
with the two boundaries merged into one. `xTensor` is defined by Hadamard
conjugation for the same reason `xSpiderSem` is.
-/

namespace SpLean.Hypergraph

open scoped Real

/-- One entry of the Hadamard matrix, as a leg tensor. Written as "minus one
when every leg is `true`" rather than as a two-argument function so it is
manifestly leg-order agnostic like the others; only `k = 2` is meaningful. -/
noncomputable def hadTensor {k : ℕ} (v : Bits k) : ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (if ∀ i, v i = true then -1 else 1)

/-- A Z spider's leg tensor. -/
noncomputable def zTensor {Φ : Type} (expI : Φ → ℂ) (φ : Φ) {k : ℕ} (v : Bits k) : ℂ :=
  (if ∀ i, v i = false then 1 else 0) + expI φ * (if ∀ i, v i = true then 1 else 0)

/-- An X spider's leg tensor: a Z spider conjugated by a Hadamard on every leg. -/
noncomputable def xTensor {Φ : Type} (expI : Φ → ℂ) (φ : Φ) {k : ℕ} (v : Bits k) : ℂ :=
  ∑ v' : Bits k, (∏ i, hadTensor ![v i, v' i]) * zTensor expI φ v'

/-- The tensor a box contributes, given the bits on its legs. -/
noncomputable def Label.tensor {Φ : Type} (expI : Φ → ℂ) :
    Label Φ → {k : ℕ} → Bits k → ℂ
  | .spider .Z φ => fun v => zTensor expI φ v
  | .spider .X φ => fun v => xTensor expI φ v
  | .hadamard => fun v => hadTensor v

/-- The bits an assignment puts on a box's legs. -/
def Box.bits {Φ : Type} {w : ℕ} (b : Box Φ w) (a : Fin w → Bool) : Bits b.arity :=
  fun i => a (b.legs i)

/-- Denotation of a hypergraph.

Sum over assignments of a bit to every wire, keeping those that agree with the
boundary and respect the identifications, and multiply the boxes' tensors. -/
noncomputable def Hyp.sem {Φ : Type} (expI : Φ → ℂ) {n m : ℕ} (H : Hyp Φ n m)
    (f : Bits n) (g : Bits m) : ℂ :=
  ∑ a : Fin H.wires → Bool,
    (if (∀ i, a (H.inputs i) = f i) ∧ (∀ j, a (H.outputs j) = g j) then 1 else 0) *
      (if H.Sat a then 1 else 0) *
      ∏ b, Label.tensor expI (H.boxes b).label ((H.boxes b).bits a)

/-- `sem` as a sum over just the assignments that respect the identifications.
The `ids` indicator only ever kills terms, so dropping it and restricting the
sum is the same thing — and the restricted form is what an isomorphism can be
transported along, since its two wire maps are inverse only on these. -/
theorem Hyp.sem_eq_sum_sat {Φ : Type} (expI : Φ → ℂ) {n m : ℕ} (H : Hyp Φ n m)
    (f : Bits n) (g : Bits m) :
    H.sem expI f g = ∑ a : {a : Fin H.wires → Bool // H.Sat a},
      (if (∀ i, a.1 (H.inputs i) = f i) ∧ (∀ j, a.1 (H.outputs j) = g j) then 1 else 0) *
        ∏ b, Label.tensor expI (H.boxes b).label ((H.boxes b).bits a.1) := by
  rw [Hyp.sem, ← Finset.sum_subset (Finset.filter_subset H.Sat Finset.univ)
    (fun a _ ha => by
      have : ¬ H.Sat a := by simpa using ha
      simp [this])]
  rw [Finset.sum_subtype (p := H.Sat) _ (fun x => by simp)]
  exact Finset.sum_congr rfl fun a _ => by rw [if_pos a.2, mul_one]

/-! ## Reindexing legs

A box's legs are indexed by `Fin b.arity`, but nothing about a diagram fixes
that indexing: an isomorphism is free to match a box's legs to another's in any
order. These say the tensors do not notice, which is what licenses that freedom
and, in the end, the spider symmetry the term calculus cannot express.

Everything is stated across *two* arities related by an `Equiv` rather than as
invariance under `Equiv.Perm`, because that is the shape `Iso` produces: it
matches `Fin b₁.arity` with `Fin b₂.arity` without either being canonical. -/

/-- Two leg assignments matched by a reindexing agree on "every leg is `b`". -/
theorem forall_bits_congr {k₁ k₂ : ℕ} (σ : Fin k₁ ≃ Fin k₂) {v₁ : Bits k₁} {v₂ : Bits k₂}
    (h : ∀ i, v₁ i = v₂ (σ i)) (b : Bool) : (∀ i, v₁ i = b) ↔ (∀ j, v₂ j = b) := by
  constructor
  · intro hv j
    rw [← σ.apply_symm_apply j, ← h]
    exact hv _
  · intro hv i
    rw [h i]
    exact hv _

theorem zTensor_congr {Φ : Type} (expI : Φ → ℂ) (φ : Φ) {k₁ k₂ : ℕ} (σ : Fin k₁ ≃ Fin k₂)
    {v₁ : Bits k₁} {v₂ : Bits k₂} (h : ∀ i, v₁ i = v₂ (σ i)) :
    zTensor expI φ v₁ = zTensor expI φ v₂ := by
  simp only [zTensor, forall_bits_congr σ h]

theorem hadTensor_congr {k₁ k₂ : ℕ} (σ : Fin k₁ ≃ Fin k₂)
    {v₁ : Bits k₁} {v₂ : Bits k₂} (h : ∀ i, v₁ i = v₂ (σ i)) :
    hadTensor v₁ = hadTensor v₂ := by
  simp only [hadTensor, forall_bits_congr σ h]

theorem xTensor_congr {Φ : Type} (expI : Φ → ℂ) (φ : Φ) {k₁ k₂ : ℕ} (σ : Fin k₁ ≃ Fin k₂)
    {v₁ : Bits k₁} {v₂ : Bits k₂} (h : ∀ i, v₁ i = v₂ (σ i)) :
    xTensor expI φ v₁ = xTensor expI φ v₂ := by
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl Bool)) _ _ fun v' => ?_
  have hv' : ∀ i, v' i = (Equiv.arrowCongr σ (Equiv.refl Bool) v') (σ i) := by
    intro i; simp [Equiv.arrowCongr]
  rw [zTensor_congr expI φ σ hv']
  congr 1
  refine Fintype.prod_equiv σ _ _ fun i => ?_
  rw [h i, hv' i]

theorem Label.tensor_congr {Φ : Type} (expI : Φ → ℂ) (L : Label Φ) {k₁ k₂ : ℕ}
    (σ : Fin k₁ ≃ Fin k₂) {v₁ : Bits k₁} {v₂ : Bits k₂} (h : ∀ i, v₁ i = v₂ (σ i)) :
    Label.tensor expI L v₁ = Label.tensor expI L v₂ := by
  cases L with
  | spider c φ =>
      cases c with
      | Z => exact zTensor_congr expI φ σ h
      | X => exact xTensor_congr expI φ σ h
  | hadamard => exact hadTensor_congr σ h

end SpLean.Hypergraph
