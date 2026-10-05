import SpLean.Algebraic.Hypergraph.Defs
import SpLean.Algebraic.Semantics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Fin

/-!
# Denotation of a hypergraph

Each wire carries one bit, so an assignment of values to the wires of `H` is a
function `Fin H.wires → Bool`. The denotation sums over all such assignments.
An assignment contributes only if it agrees with the boundary values `f` and
`g` and gives each identified pair of wires the same value; its contribution is
then the product of every box's tensor, applied to the bits on that box's legs.

Every tensor here is invariant under permuting its legs. This is what makes it
sound for a box to have no distinguished leg order. A Z spider is `1` when all
its legs are `false`, `φ.expI` when all are `true`, and `0` otherwise; it treats
inputs and outputs alike. That is `zSpiderSem` from
`SpLean/Algebraic/Semantics.lean` with its input and output bits merged into a
single list. `xTensor` is a Z spider conjugated by Hadamards, matching how
`xSpiderSem` is defined there.
-/

namespace SpLean.Algebraic.Hypergraph

open scoped Real

/-- One entry of the Hadamard matrix, as a leg tensor: `1/√2`, negated when
every leg is `true`. Stated over any number of legs, rather than as a function
of two bits, so that it is visibly independent of leg order like the other
tensors. Only `k = 2` corresponds to a Hadamard. -/
noncomputable def hadTensor {k : ℕ} (v : Wires k) : ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (if ∀ i, v i = true then -1 else 1)

/-- A Z spider's leg tensor. -/
noncomputable def zTensor (φ : AlgPhase) {k : ℕ} (v : Wires k) : ℂ :=
  (if ∀ i, v i = false then 1 else 0) + φ.expI * (if ∀ i, v i = true then 1 else 0)

/-- An X spider's leg tensor: a Z spider conjugated by a Hadamard on every leg. -/
noncomputable def xTensor (φ : AlgPhase) {k : ℕ} (v : Wires k) : ℂ :=
  ∑ v' : Wires k, (∏ i, hadTensor ![v i, v' i]) * zTensor φ v'

/-- The tensor a box contributes, given the bits on its legs. -/
noncomputable def Label.tensor :
    Label → {k : ℕ} → Wires k → ℂ
  | .spider .Z φ => fun v => zTensor φ v
  | .spider .X φ => fun v => xTensor φ v
  | .hadamard => fun v => hadTensor v

/-- The bits an assignment puts on a box's legs. -/
def Box.bits {w : ℕ} (b : Box w) (a : Fin w → Bool) : Wires b.arity :=
  fun i => a (b.legs i)

/-- Denotation of a hypergraph, as the matrix entry for input bits `f` and
output bits `g`.

Sums over assignments of a bit to every wire. Each assignment that agrees with
`f` and `g` on the boundary and gives identified wires equal values contributes
the product of the boxes' tensors. -/
noncomputable def Hyp.sem {n m : ℕ} (H : Hyp n m)
    (f : Wires n) (g : Wires m) : ℂ :=
  ∑ a : Fin H.wires → Bool,
    (if (∀ i, a (H.inputs i) = f i) ∧ (∀ j, a (H.outputs j) = g j) then 1 else 0) *
      (if ∀ k, a (H.ids k).1 = a (H.ids k).2 then 1 else 0) *
      ∏ b, Label.tensor (H.boxes b).label ((H.boxes b).bits a)

/-! ## Reindexing legs

A box's legs are indexed by `Fin b.arity`, but the diagram it represents does
not depend on that indexing, so an isomorphism of hypergraphs may match one
box's legs with another's in any order. The lemmas below show that every tensor
gives the same value under any such reindexing. This is what justifies
treating legs as unordered, and with it full spider symmetry, which `ZX` terms
can only reach by bending wires.

The lemmas relate two arities `k₁` and `k₂` through an equivalence
`Fin k₁ ≃ Fin k₂`, rather than stating invariance under a permutation
`Equiv.Perm (Fin k)`. A hypergraph isomorphism matches `Fin b₁.arity` with
`Fin b₂.arity` for two boxes whose arities are equal but not definitionally so,
and this form applies to it directly. -/

/-- If two leg assignments agree up to the reindexing `σ`, then every leg of
one is `b` exactly when every leg of the other is. -/
theorem forall_bits_congr {k₁ k₂ : ℕ} (σ : Fin k₁ ≃ Fin k₂) {v₁ : Wires k₁} {v₂ : Wires k₂}
    (h : ∀ i, v₁ i = v₂ (σ i)) (b : Bool) : (∀ i, v₁ i = b) ↔ (∀ j, v₂ j = b) := by
  constructor
  · intro hv j
    rw [← σ.apply_symm_apply j, ← h]
    exact hv _
  · intro hv i
    rw [h i]
    exact hv _

theorem zTensor_congr (φ : AlgPhase) {k₁ k₂ : ℕ} (σ : Fin k₁ ≃ Fin k₂)
    {v₁ : Wires k₁} {v₂ : Wires k₂} (h : ∀ i, v₁ i = v₂ (σ i)) :
    zTensor φ v₁ = zTensor φ v₂ := by
  simp only [zTensor, forall_bits_congr σ h]

theorem hadTensor_congr {k₁ k₂ : ℕ} (σ : Fin k₁ ≃ Fin k₂)
    {v₁ : Wires k₁} {v₂ : Wires k₂} (h : ∀ i, v₁ i = v₂ (σ i)) :
    hadTensor v₁ = hadTensor v₂ := by
  simp only [hadTensor, forall_bits_congr σ h]

theorem xTensor_congr (φ : AlgPhase) {k₁ k₂ : ℕ} (σ : Fin k₁ ≃ Fin k₂)
    {v₁ : Wires k₁} {v₂ : Wires k₂} (h : ∀ i, v₁ i = v₂ (σ i)) :
    xTensor φ v₁ = xTensor φ v₂ := by
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl Bool)) _ _ fun v' => ?_
  have hv' : ∀ i, v' i = (Equiv.arrowCongr σ (Equiv.refl Bool) v') (σ i) := by
    intro i; simp [Equiv.arrowCongr]
  rw [zTensor_congr φ σ hv']
  congr 1
  refine Fintype.prod_equiv σ _ _ fun i => ?_
  rw [h i, hv' i]

theorem Label.tensor_congr (L : Label) {k₁ k₂ : ℕ}
    (σ : Fin k₁ ≃ Fin k₂) {v₁ : Wires k₁} {v₂ : Wires k₂} (h : ∀ i, v₁ i = v₂ (σ i)) :
    Label.tensor L v₁ = Label.tensor L v₂ := by
  cases L with
  | spider c φ =>
      cases c with
      | Z => exact zTensor_congr φ σ h
      | X => exact xTensor_congr φ σ h
  | hadamard => exact hadTensor_congr σ h

end SpLean.Algebraic.Hypergraph
