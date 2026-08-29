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
    (bs : List (Box Φ w)) : List (Box Φ w') :=
  bs.map fun b => { b with legs := e ∘ b.legs }

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
      { wires := 2, boxes := [{ label := .hadamard, arity := 2, legs := id }], ids := [],
        inputs := fun _ => 0, outputs := fun _ => 1 }
  | n, m, .spider c _ _ φ =>
      { wires := n + m,
        boxes := [{ label := .spider c.toHypColour φ, arity := n + m, legs := id }],
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

/-- A boundary assignment built by `Fin.addCases` is all-`b` exactly when both
halves are. The bridge between a hypergraph's single wire assignment and
`ZX.sem`'s split `f`/`g` pair, and the only fact the spider case needs. -/
private theorem addCases_forall_eq {n m : ℕ} (f : Wires n) (g : Wires m) (b : Bool) :
    (∀ i : Fin (n + m), Fin.addCases f g i = b) ↔ (∀ i, f i = b) ∧ (∀ j, g j = b) := by
  constructor
  · intro h
    exact ⟨fun i => by simpa using h (Fin.castAdd m i), fun j => by simpa using h (Fin.natAdd n j)⟩
  · rintro ⟨h₁, h₂⟩ i
    induction i using Fin.addCases <;> simp [h₁, h₂]

theorem sem_toHyp_zSpider (n m : ℕ) (φ : AlgPhase) (f : Wires n) (g : Wires m) :
    ((ZX.spider .Z n m φ).toHyp).sem AlgPhase.expI f g = (ZX.spider .Z n m φ).sem f g := by
  simp only [ZX.toHyp, Hyp.sem, ZX.sem, zSpiderSem, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, if_true]
  rw [Finset.sum_eq_single (Fin.addCases f g)]
  · simp only [AlgSpColor.toHypColour, Label.tensor, Box.bits, zTensor, id_eq,
      Fin.addCases_left, Fin.addCases_right, implies_true, and_self, if_true, one_mul,
      addCases_forall_eq]
  · intro a _ hne
    have : ¬ ((∀ i, a (Fin.castAdd m i) = f i) ∧ (∀ j, a (Fin.natAdd n j) = g j)) := by
      rintro ⟨h₁, h₂⟩
      exact hne (funext fun i => by induction i using Fin.addCases <;> simp [h₁, h₂])
    simp [this]
  · simp

theorem sem_toHyp_wire_compose (f g : Wires 1) :
    ((ZX.wire ≫ ZX.wire).toHyp).sem AlgPhase.expI f g = (ZX.wire ≫ ZX.wire).sem f g := by
  simp only [ZX.toHyp, Hyp.sem, ZX.sem, embedBoxes, embedIds, List.map_nil, List.nil_append,
    List.prod_nil, mul_one, List.ofFn_succ, List.ofFn_zero,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq, Fin.forall_fin_one]
  rw [sum_wires2, sum_wires1]
  cases hf : f 0 <;> cases hg : g 0 <;> simp [zeroAmpl, oneAmpl]

end SpLean.Algebraic
