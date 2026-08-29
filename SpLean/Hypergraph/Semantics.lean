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
      (if ∀ p ∈ H.ids, a p.1 = a p.2 then 1 else 0) *
      (H.boxes.map (fun b => Label.tensor expI b.label (b.bits a))).prod

end SpLean.Hypergraph
