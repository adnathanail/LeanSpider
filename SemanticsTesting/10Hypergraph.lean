import SpLean.Algebraic

open SpLean.Algebraic SpLean.Hypergraph

/-!
# Equivalence by hypergraph isomorphism

`SemanticsTesting/09Rules.lean` proves `Gate.CNOT ≈zx Gate.CNOT'` twice: once
by computing both denotations, once by a twelve-line derivation that rests on
two stubbed rules. Here it is one tactic call, resting on nothing.

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

/-! ## Edge cases

Degenerate and awkward shapes, kept as regression tests. Each of these found
nothing wrong when it was first run, except the last group. -/

/-- Nothing at all: no wires, no boxes. -/
example : (ZX.empty : ZX 0 0) ≈zx ZX.empty := by zx_iso

/-- Different numbers of wires on the two sides — two in series against one.
This is the case a plain bijection could not handle, and the reason `Iso` is
stated up to `Hyp.Rel`. -/
example : (ZX.wire ≫ ZX.wire) ≈zx ZX.wire := by zx_iso

/-- A scalar: a box with no legs and no boundary to pin it. -/
example : (ZX.spider .Z 0 0 : ZX 0 0) ≈zx ZX.spider .Z 0 0 := by zx_iso

/-- Two boxes with the same label, so the search cannot tell them apart by
label alone and has to backtrack over which is which. -/
example : ((Gate.T ⊗ Gate.T) ≫ (Gate.S ⊗ Gate.S)) ≈zx ((Gate.T ≫ Gate.S) ⊗ (Gate.T ≫ Gate.S)) := by
  zx_iso

/-- A term carrying a `ZX.cast`. Casts change no wire and no generator, so they
vanish at the hypergraph level — `toHyp` reduces through them. -/
example : (ZX.cast (Nat.zero_add 1) (Nat.zero_add 1) (ZX.empty ⊗ ZX.wire)) ≈zx ZX.wire := by zx_iso

/-- `nWire`, which is a definition by recursion rather than a constructor. -/
example : (ZX.nWire 2 ≫ (Gate.T ⊗ Gate.S)) ≈zx (Gate.T ⊗ Gate.S) := by zx_iso

/-- A disconnected component: a scalar sitting beside a wire, so some wire
classes are reached by neither the boundary nor any box. -/
example : ((ZX.wire ⊗ (ZX.spider .Z 0 0 : ZX 0 0)) : ZX 1 1)
    ≈zx (((ZX.spider .Z 0 0 : ZX 0 0) ⊗ ZX.wire) : ZX 1 1) := by zx_iso

/-- Four spiders a side, re-associated: big enough to notice if the search
starts to cost something. -/
example :
    ((((ZX.spider .Z 1 2 ⊗ ZX.wire) ≫ (ZX.wire ⊗ ZX.spider .X 2 1 : ZX 3 2))
        ≫ ((ZX.spider .Z 1 2 ⊗ ZX.wire) ≫ (ZX.wire ⊗ ZX.spider .X 2 1 : ZX 3 2))) : ZX 2 2)
      ≈zx (((ZX.spider .Z 1 2 ⊗ ZX.wire) ≫ ((ZX.wire ⊗ ZX.spider .X 2 1 : ZX 3 2)
        ≫ ((ZX.spider .Z 1 2 ⊗ ZX.wire) ≫ (ZX.wire ⊗ ZX.spider .X 2 1 : ZX 3 2)))) : ZX 2 2) := by
  zx_iso

/-! ### When it must refuse

The tactic declining is as much a part of its behaviour as it succeeding, so
the failures are pinned here too. Note the third: it is a *true* equivalence
that `zx_iso` correctly refuses, because fusion changes the diagram and this
tactic only ever answers "same diagram?". -/

/-- error: zx_iso: no isomorphism found between the hypergraphs of
  Gate.CNOT
and
  Gate.NOTC
-/
#guard_msgs in
example : Gate.CNOT ≈zx Gate.NOTC := by zx_iso

/-- error: zx_iso: no isomorphism found between the hypergraphs of
  Gate.T
and
  Gate.S
-/
#guard_msgs in
example : Gate.T ≈zx Gate.S := by zx_iso

/-- error: zx_iso: no isomorphism found between the hypergraphs of
  Gate.T ≫ Gate.T
and
  Gate.S
-/
#guard_msgs in
example : (Gate.T ≫ Gate.T) ≈zx Gate.S := by zx_iso

/-- error: zx_iso: needs closed diagrams, but
  ZX.spider AlgSpColor.Z 1 1 α ≫ ZX.wire
mentions a variable. A diagram parameterised by a phase has no hypergraph to compute; prove it by rewriting instead.
-/
#guard_msgs in
example (α : AlgPhase) : (ZX.spider .Z 1 1 α ≫ ZX.wire) ≈zx (ZX.wire ≫ ZX.spider .Z 1 1 α) := by
  zx_iso

/-- error: zx_iso: goal is not of the form `x ≈zx y`, but
  1 = 1
-/
#guard_msgs in
example : (1 : ℕ) = 1 := by zx_iso

/-! ## What the tactic emits

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
