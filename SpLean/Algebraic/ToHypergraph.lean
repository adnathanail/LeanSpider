import SpLean.Algebraic.Semantics
import SpLean.Algebraic.Rules.Lemmas
import SpLean.Hypergraph

/-!
# Lowering an algebraic term to a hypergraph

`toHyp` walks a `ZX n m` and produces the hypergraph of `SpLean/Hypergraph/`:
wires become vertices, generators become boxes. The point of the exercise is
`sem_toHyp` — that the lowering does not change the denotation — after which
two terms with isomorphic hypergraphs are equivalent. See
`SpLean/Hypergraph/PLAN.md`; this file is the phase 0 spike.

Composition is the only interesting case: it takes the disjoint union and
*records* that `a`'s output wire `i` is `b`'s input wire `i`, rather than
renumbering. `Hyp.sem`'s delta on each recorded pair is what keeps the merged
wire from being summed over twice.
-/

namespace SpLean.Algebraic

open SpLean.Hypergraph

/-- Colours translate one for one. -/
def AlgSpColor.toHypColour : AlgSpColor → Hypergraph.Colour
  | .Z => .Z
  | .X => .X

private def embedBoxes {Φ : Type} {w w' : ℕ} (e : Fin w → Fin w')
    (bs : List (Label Φ × List (Fin w))) : List (Label Φ × List (Fin w')) :=
  bs.map fun b => (b.1, b.2.map e)

private def embedIds {w w' : ℕ} (e : Fin w → Fin w')
    (is : List (Fin w × Fin w)) : List (Fin w' × Fin w') :=
  is.map fun p => (e p.1, e p.2)

/-- The hypergraph of an algebraic term. -/
def ZX.toHyp : {n m : ℕ} → ZX n m → Hyp AlgPhase n m
  | _, _, .empty =>
      { wires := 0, boxes := [], ids := [], inputs := Fin.elim0, outputs := Fin.elim0 }
  | _, _, .wire =>
      { wires := 1, boxes := [], ids := [], inputs := fun _ => 0, outputs := fun _ => 0 }
  | _, _, .hadamard =>
      { wires := 2, boxes := [(.hadamard, [0, 1])], ids := [],
        inputs := fun _ => 0, outputs := fun _ => 1 }
  | n, m, .spider c _ _ φ =>
      { wires := n + m,
        boxes := [(.spider c.toHypColour φ, List.finRange (n + m))],
        ids := [],
        inputs := Fin.castAdd m, outputs := Fin.natAdd n }
  | _, _, .stack a b =>
      let A := a.toHyp
      let B := b.toHyp
      { wires := A.wires + B.wires,
        boxes := embedBoxes (Fin.castAdd B.wires) A.boxes
                  ++ embedBoxes (Fin.natAdd A.wires) B.boxes,
        ids := embedIds (Fin.castAdd B.wires) A.ids
                ++ embedIds (Fin.natAdd A.wires) B.ids,
        inputs := Fin.addCases (fun i => Fin.castAdd B.wires (A.inputs i))
                               (fun i => Fin.natAdd A.wires (B.inputs i)),
        outputs := Fin.addCases (fun j => Fin.castAdd B.wires (A.outputs j))
                                (fun j => Fin.natAdd A.wires (B.outputs j)) }
  | _, _, .compose (m := m) a b =>
      let A := a.toHyp
      let B := b.toHyp
      { wires := A.wires + B.wires,
        boxes := embedBoxes (Fin.castAdd B.wires) A.boxes
                  ++ embedBoxes (Fin.natAdd A.wires) B.boxes,
        ids := embedIds (Fin.castAdd B.wires) A.ids
                ++ embedIds (Fin.natAdd A.wires) B.ids
                ++ List.ofFn (fun i : Fin m =>
                     (Fin.castAdd B.wires (A.outputs i), Fin.natAdd A.wires (B.inputs i))),
        inputs := fun i => Fin.castAdd B.wires (A.inputs i),
        outputs := fun j => Fin.natAdd A.wires (B.outputs j) }

/-! ## Phase 0 targets

Three instances of `sem_toHyp`, chosen to exercise each part of the encoding
before the general theorem is attempted: a bare wire (a vertex pinned twice by
the boundary), a spider (the box tensor and its leg list), and `wire ≫ wire`
(the smallest term where composition merges a wire at all — the case that
catches a merge which leaves a wire summed over freely). -/

theorem sem_toHyp_wire (f g : Wires 1) :
    (ZX.wire.toHyp).sem AlgPhase.expI f g = ZX.wire.sem f g := by
  simp only [ZX.toHyp, Hyp.sem, ZX.sem, List.map_nil, List.prod_nil, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, if_true, mul_one, Fin.forall_fin_one]
  rw [sum_wires1]
  cases hf : f 0 <;> cases hg : g 0 <;> simp [zeroAmpl, oneAmpl]

end SpLean.Algebraic
