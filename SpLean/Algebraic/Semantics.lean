import SpLean.Algebraic.ZX

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
-/

namespace SpLean.Algebraic

/-- A boundary assignment: one Boolean per open wire. -/
abbrev Wires (n : ℕ) := Fin n → Bool

/-- Tensor of a Z spider: `1` on the all-`false` boundary, `φ.expI` on the
all-`true` boundary, `0` elsewhere. When `n = m = 0` both indicators fire and
the scalar is `1 + φ.expI`, as it should be. -/
noncomputable def zSpiderSem (φ : AlgPhase) {n m : ℕ} (f : Wires n) (g : Wires m) : ℂ :=
  (if (∀ i, f i = false) ∧ (∀ j, g j = false) then 1 else 0)
    + φ.expI *
        (if (∀ i, f i = true) ∧ (∀ j, g j = true) then 1 else 0)

/-- One matrix entry of the Hadamard gate. -/
noncomputable def hadSem (a b : Bool) : ℂ :=
  if a && b then -((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- Tensor of an X spider: a Z spider conjugated by Hadamards on every wire. -/
noncomputable def xSpiderSem (φ : AlgPhase) {n m : ℕ} (f : Wires n) (g : Wires m) : ℂ :=
  ∑ f' : Wires n, ∑ g' : Wires m,
    (∏ i, hadSem (f i) (f' i)) * zSpiderSem φ f' g' * (∏ j, hadSem (g' j) (g j))

/-- Denotation of an algebraic ZX term as a boundary tensor.
`compose` sums over the shared internal boundary; `stack` splits the boundary
assignment between the two halves. -/
noncomputable def ZX.sem : {n m : ℕ} → ZX n m → Wires n → Wires m → ℂ
  | _, _, .empty, _, _ => 1                                  -- Empty diagram = 1
  | _, _, .wire, f, g => if f 0 = g 0 then 1 else 0          -- Wire = identity matrix
  | _, _, .hadamard, f, g => hadSem (f 0) (g 0)
  | _, _, .spider .Z _ _ φ, f, g => zSpiderSem φ f g
  | _, _, .spider .X _ _ φ, f, g => xSpiderSem φ f g
  | _, _, .swap, f, g => if f 0 = g 1 ∧ f 1 = g 0 then 1 else 0 -- Swap = permutation matrix
  | _, _, .compose a b, f, h => ∑ g, a.sem f g * b.sem g h   -- Composition = tensor contraction
  | _, _, .stack a b, f, g =>
      -- Split up the responsibility for wire indexes across the two stacked diagrams
      a.sem (fun i => f (Fin.castAdd _ i)) (fun j => g (Fin.castAdd _ j)) *
        b.sem (fun i => f (Fin.natAdd _ i)) (fun j => g (Fin.natAdd _ j))

end SpLean.Algebraic
