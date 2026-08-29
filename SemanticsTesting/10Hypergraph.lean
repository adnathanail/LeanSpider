import SpLean.Algebraic

open SpLean.Algebraic SpLean.Hypergraph

/-!
# Equivalence by hypergraph isomorphism

`SemanticsTesting/09Rules.lean` proves `Gate.CNOT ≈zx Gate.CNOT'` twice: once
by computing both denotations, once by a twelve-line derivation. Here it is a
third way — the two terms have isomorphic hypergraphs, so they are equivalent,
and the isomorphism's conditions are all `decide`.

The two hypergraphs, as `toHyp` builds them (wires, then boxes as
`(colour, legs)`, then identifications, inputs and outputs):

    CNOT   8  [(Z, [0,1,2]), (X, [5,6,7])]  [(1,4), (2,5), (3,6)]  [0,3]  [4,7]
    CNOT'  8  [(X, [1,2,3]), (Z, [4,5,6])]  [(0,4), (2,5), (3,7)]  [0,1]  [6,7]

Neither is a relabelling of the other — in `CNOT` the Z spider's input leg *is*
the boundary input wire, while in `CNOT'` the boundary input is a separate wire
identified with that leg. It is the *classes* that correspond, which is why
`Iso` is stated up to `Hyp.Rel` throughout:

    CNOT   {0}  {1,4}  {2,5}  {3,6}  {7}
    CNOT'  {0,4}  {6}   {2,5}  {1}    {3,7}

Reading down: the Z's input, the Z's output to the boundary, the wire joining
the two spiders, the X's other input, and the X's output. The maps below send
each class to a representative of its partner, and the box permutation swaps
the two spiders since `toHyp` lists them in opposite orders.
-/

theorem cnot_cnot_iso : Gate.CNOT ≈zx Gate.CNOT' :=
  ZX.Equiv.of_hyp_iso <|
    Iso.ofRepEq
      (wire := (![4, 6, 5, 1, 6, 5, 1, 7] : Fin 8 → Fin 8))
      (wireInv := (![0, 6, 5, 7, 0, 5, 4, 7] : Fin 8 → Fin 8))
      (boxPerm := (Equiv.swap 0 1 : Equiv.Perm (Fin 2)))
      (legPerm := fun i =>
        match i with
        | ⟨0, _⟩ => (Equiv.swap 1 2 : Equiv.Perm (Fin 3))
        | ⟨1, _⟩ => (Equiv.swap 0 1 : Equiv.Perm (Fin 3)))
      (hleft := by decide)
      (hright := by decide)
      (hids₁ := by decide)
      (hids₂ := by decide)
      (hin := by decide)
      (hout := by decide)
      (hlabel := by decide)
      (hlegs := by decide)
