import SpLean.Algebraic.Semantics
import SpLean.Algebraic.Rules.Lemmas
import SpLean.Algebraic.Hypergraph.Semantics

/-!
# Lowering an algebraic term to a hypergraph

`ZX.toHyp` turns a `ZX n m` term into the hypergraph defined in `Defs.lean`: each wire of the diagram becomes a vertex and each
generator becomes a hyperedge. The lowering is meant to preserve the denotation,
`(a.toHyp).sem = a.sem`, so that two terms whose hypergraphs are isomorphic
can be shown equivalent without a rewriting derivation.
`PLAN.md`, in this folder, describes the overall approach.

Most constructors lower directly. Stacking is a disjoint union of the two
hypergraphs, with the second one's wires numbered after the first's.
Composition is also a disjoint union, but it additionally records each pair
(`a`'s output wire `i`, `b`'s input wire `i`) in `ids` instead of merging and
renumbering the wires. `Hyp.sem` forces each recorded pair to carry the same
value, so the two halves of a merged wire are not summed over independently.
-/

namespace SpLean.Algebraic

open Hypergraph

/-- Moves an edge into a larger wire set along `e`. -/
private def embedEdge {w w' : ℕ} (e : Fin w → Fin w') (b : Hyp.Edge w) : Hyp.Edge w' :=
  { b with legs := e ∘ b.legs }

/-- Moves an identified pair into a larger wire set along `e`. -/
private def embedId {w w' : ℕ} (e : Fin w → Fin w') (p : Fin w × Fin w) : Fin w' × Fin w' :=
  (e p.1, e p.2)

/-- The hypergraph of an algebraic term.

A `wire` is a single vertex that is both the input and the output, and a
`swap` is two vertices with no edges, its crossing expressed entirely by the
boundary maps. A spider is one edge whose legs are all `n + m` of its wires,
inputs first. -/
def ZX.toHyp : {n m : ℕ} → ZX n m → Hyp n m
  | _, _, .empty =>
      { wires := 0, edgeCount := 0, edges := Fin.elim0, idCount := 0, ids := Fin.elim0,
        inputs := Fin.elim0, outputs := Fin.elim0 }
  | _, _, .wire =>
      { wires := 1, edgeCount := 0, edges := Fin.elim0, idCount := 0, ids := Fin.elim0,
        inputs := fun _ => 0, outputs := fun _ => 0 }
  | _, _, .hadamard =>
      { wires := 2,
        edgeCount := 1, edges := fun _ => { label := .hadamard, arity := 2, legs := id },
        idCount := 0, ids := Fin.elim0,
        inputs := fun _ => 0, outputs := fun _ => 1 }
  | n, m, .spider c _ _ φ =>
      { wires := n + m,
        edgeCount := 1,
        edges := fun _ => { label := .spider c φ, arity := n + m, legs := id },
        idCount := 0, ids := Fin.elim0,
        inputs := Fin.castAdd m, outputs := Fin.natAdd n }
  | _, _, .swap =>
      { wires := 2, edgeCount := 0, edges := Fin.elim0, idCount := 0, ids := Fin.elim0,
        inputs := id, outputs := Fin.rev }
  | _, _, .stack a b =>
      let A := a.toHyp
      let B := b.toHyp
      { wires := A.wires + B.wires,
        edgeCount := A.edgeCount + B.edgeCount,
        edges := Fin.addCases (fun i => embedEdge (Fin.castAdd B.wires) (A.edges i))
                              (fun i => embedEdge (Fin.natAdd A.wires) (B.edges i)),
        idCount := A.idCount + B.idCount,
        ids := Fin.addCases (fun i => embedId (Fin.castAdd B.wires) (A.ids i))
                            (fun i => embedId (Fin.natAdd A.wires) (B.ids i)),
        inputs := Fin.addCases (fun i => Fin.castAdd B.wires (A.inputs i))
                               (fun i => Fin.natAdd A.wires (B.inputs i)),
        outputs := Fin.addCases (fun j => Fin.castAdd B.wires (A.outputs j))
                                (fun j => Fin.natAdd A.wires (B.outputs j)) }
  | _, _, .compose (m := m) a b =>
      let A := a.toHyp
      let B := b.toHyp
      { wires := A.wires + B.wires,
        edgeCount := A.edgeCount + B.edgeCount,
        edges := Fin.addCases (fun i => embedEdge (Fin.castAdd B.wires) (A.edges i))
                              (fun i => embedEdge (Fin.natAdd A.wires) (B.edges i)),
        idCount := A.idCount + B.idCount + m,
        ids := Fin.addCases
                 (Fin.addCases (fun i => embedId (Fin.castAdd B.wires) (A.ids i))
                               (fun i => embedId (Fin.natAdd A.wires) (B.ids i)))
                 (fun i : Fin m =>
                    (Fin.castAdd B.wires (A.outputs i), Fin.natAdd A.wires (B.inputs i))),
        inputs := fun i => Fin.castAdd B.wires (A.inputs i),
        outputs := fun j => Fin.natAdd A.wires (B.outputs j) }

/-! ## Denotation is preserved on small cases

The lowering preserves the denotation for three terms, each exercising a
different part of the encoding:

- `wire`: a single vertex fixed by both the input and the output boundary;
- a Z spider: an edge's tensor applied to its legs;
- `wire ≫ wire`: the smallest term in which composition identifies two wires.
  If the identification failed to tie the two wires together, the free wire
  would be summed over and the denotation would come out doubled. -/

theorem sem_toHyp_wire (f g : Wires 1) :
    (ZX.wire.toHyp).sem f g = ZX.wire.sem f g := by
  simp only [ZX.toHyp, Hyp.sem, ZX.sem, IsEmpty.forall_iff, if_true, mul_one, Fin.forall_fin_one]
  rw [sum_wires1]
  cases hf : f 0 <;> cases hg : g 0 <;> simp [zeroAmpl, oneAmpl]

/-- A boundary assignment built by `Fin.addCases` is all-`b` exactly when both
halves are. A spider's edge sees a single assignment to all `n + m` legs, while
`zSpiderSem` takes the inputs `f` and outputs `g` separately; this lemma
connects the two in the spider case. -/
private theorem addCases_forall_eq {n m : ℕ} (f : Wires n) (g : Wires m) (b : Bool) :
    (∀ i : Fin (n + m), Fin.addCases f g i = b) ↔ (∀ i, f i = b) ∧ (∀ j, g j = b) := by
  constructor
  · intro h
    exact ⟨fun i => by simpa using h (Fin.castAdd m i), fun j => by simpa using h (Fin.natAdd n j)⟩
  · rintro ⟨h₁, h₂⟩ i
    induction i using Fin.addCases <;> simp [h₁, h₂]

theorem sem_toHyp_zSpider (n m : ℕ) (φ : AlgPhase) (f : Wires n) (g : Wires m) :
    ((ZX.spider .Z n m φ).toHyp).sem f g = (ZX.spider .Z n m φ).sem f g := by
  simp only [ZX.toHyp, Hyp.sem, ZX.sem, zSpiderSem, mul_one, IsEmpty.forall_iff, if_true]
  rw [Finset.sum_eq_single (Fin.addCases f g)]
  · simp only [Hyp.Label.tensor, Hyp.Edge.bits, zTensor, id_eq,
      Fin.addCases_left, Fin.addCases_right, implies_true, and_self, if_true, one_mul,
      Fin.prod_univ_one, addCases_forall_eq]
  · intro a _ hne
    have : ¬ ((∀ i, a (Fin.castAdd m i) = f i) ∧ (∀ j, a (Fin.natAdd n j) = g j)) := by
      rintro ⟨h₁, h₂⟩
      exact hne (funext fun i => by induction i using Fin.addCases <;> simp [h₁, h₂])
    simp [this]
  · simp

theorem sem_toHyp_wire_compose (f g : Wires 1) :
    ((ZX.wire ≫ ZX.wire).toHyp).sem f g = (ZX.wire ≫ ZX.wire).sem f g := by
  simp only [ZX.toHyp, Hyp.sem, ZX.sem, Fin.forall_fin_one, Fin.addCases, embedId]
  rw [sum_wires2, sum_wires1]
  cases hf : f 0 <;> cases hg : g 0 <;> simp [zeroAmpl, oneAmpl]

end SpLean.Algebraic
