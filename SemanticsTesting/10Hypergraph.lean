import SpLean.Algebraic

open SpLean.Algebraic SpLean.Hypergraph

/-!
# Equivalence by hypergraph isomorphism

`SemanticsTesting/09Rules.lean` proves `Gate.CNOT ≈zx Gate.CNOT'` twice: once
by computing both denotations, once by a twelve-line derivation that rests on
four stubbed rules. Here it is one tactic call, resting on nothing.

`zx_iso` lowers both sides to hypergraphs, searches for an isomorphism, and
emits it as a certificate the kernel checks with `decide`. The search is
untrusted — a wrong answer costs a failed tactic, not a bad proof — so the
interesting half of the work is in `Iso.sem_eq` and `sem_toHyp`, both of which
are proved.

What this settles is the question a derivation is bad at: *do these two terms
describe the same diagram?* It says nothing about rules that change the
diagram, so fusion, colour change and the rest are still rules.
-/

theorem cnot_cnot_iso : Gate.CNOT ≈zx Gate.CNOT' := by zx_iso

/-! Three more, to show the first is not a special case. Each is an instance of
a law in `Rules/Structural.lean`, and each holds for the same reason: the two
terms bracket one diagram differently. -/

example : ((Gate.T ≫ Gate.S) ≫ Gate.Z) ≈zx (Gate.T ≫ (Gate.S ≫ Gate.Z)) := by zx_iso

example : ((Gate.T ⊗ Gate.S) ≫ (Gate.Z ⊗ Gate.X)) ≈zx ((Gate.T ≫ Gate.Z) ⊗ (Gate.S ≫ Gate.X)) := by
  zx_iso

example : (Gate.T ⊗ ZX.empty) ≈zx Gate.T := by zx_iso

/-! `zx_iso` fails rather than proving nonsense — `Gate.CNOT ≈zx Gate.NOTC`
(control on the other qubit) and `Gate.T ≈zx Gate.S` (different phase) both
report that no isomorphism was found.

## What the tactic emits

The certificate below is what the search produces for the CNOT pair, written
out. The two hypergraphs, as `toHyp` builds them — wires, then boxes as
`(colour, legs)`, then identifications, inputs and outputs:

    CNOT   8  [(Z, [0,1,2]), (X, [5,6,7])]  [(1,4), (2,5), (3,6)]  [0,3]  [4,7]
    CNOT'  8  [(X, [1,2,3]), (Z, [4,5,6])]  [(0,4), (2,5), (3,7)]  [0,1]  [6,7]

Neither is a relabelling of the other: in `CNOT` the Z spider's input leg *is*
the boundary input wire, while in `CNOT'` the boundary input is a separate wire
identified with that leg. It is the *classes* that correspond, which is why
`Iso` is stated up to `Hyp.Rel` throughout.

    CNOT   {0}    {1,4}  {2,5}  {3,6}  {7}
    CNOT'  {0,4}  {6}    {2,5}  {1}    {3,7}

Reading down: the Z's input, the Z's output to the boundary, the wire joining
the two spiders, the X's other input, and the X's output. The box permutation
swaps the two spiders, since `toHyp` lists them in opposite orders. -/
theorem cnot_cnot_iso_explicit : Gate.CNOT ≈zx Gate.CNOT' :=
  ZX.Equiv.of_hyp_iso <|
    Iso.ofTables
      (w := fun a => List.getD [4, 6, 5, 1, 6, 5, 1, 7] a 0)
      (wInv := fun a => List.getD [0, 6, 5, 7, 0, 5, 4, 7] a 0)
      (bp := fun a => List.getD [1, 0] a 0)
      (bpInv := fun a => List.getD [1, 0] a 0)
      (lp := fun i k => List.getD (List.getD [[0, 2, 1], [1, 0, 2]] i []) k 0)
      (lpInv := fun i k => List.getD (List.getD [[0, 2, 1], [1, 0, 2]] i []) k 0)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
