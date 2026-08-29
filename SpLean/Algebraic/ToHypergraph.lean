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

private def embedBox {Φ : Type} {w w' : ℕ} (e : Fin w → Fin w') (b : Box Φ w) : Box Φ w' :=
  { b with legs := e ∘ b.legs }

private def embedId {w w' : ℕ} (e : Fin w → Fin w') (p : Fin w × Fin w) : Fin w' × Fin w' :=
  (e p.1, e p.2)

/-! Both `stack` and `compose` put the two halves' boxes and identifications
side by side, each embedded into the combined wires. These name that, with
their own simp lemmas: a bare `Fin.addCases` is awkward to rewrite under a
projection (`(Fin.addCases ..).label` does not even elaborate when written by
hand), whereas a named function with `_left`/`_right` equations rewrites
predictably. -/

private def appendBoxes {Φ : Type} {w₁ w₂ b₁ b₂ : ℕ}
    (A : Fin b₁ → Box Φ w₁) (B : Fin b₂ → Box Φ w₂) : Fin (b₁ + b₂) → Box Φ (w₁ + w₂) :=
  Fin.addCases (fun i => embedBox (Fin.castAdd w₂) (A i))
               (fun i => embedBox (Fin.natAdd w₁) (B i))

@[simp] private theorem appendBoxes_left {Φ : Type} {w₁ w₂ b₁ b₂ : ℕ}
    (A : Fin b₁ → Box Φ w₁) (B : Fin b₂ → Box Φ w₂) (i : Fin b₁) :
    appendBoxes A B (Fin.castAdd b₂ i) = embedBox (Fin.castAdd w₂) (A i) := by
  simp [appendBoxes]

@[simp] private theorem appendBoxes_right {Φ : Type} {w₁ w₂ b₁ b₂ : ℕ}
    (A : Fin b₁ → Box Φ w₁) (B : Fin b₂ → Box Φ w₂) (i : Fin b₂) :
    appendBoxes A B (Fin.natAdd b₁ i) = embedBox (Fin.natAdd w₁) (B i) := by
  simp [appendBoxes]

/-! A box's bits have type `Bits b.arity`, so rewriting the box underneath
`Box.bits` is a dependent rewrite and `simp` will not do it. These move the
whole `Label.tensor _ b.label (b.bits _)` unit instead, which is well typed
however `b` is rewritten. -/

private theorem bits_embedBox {Φ : Type} {w w' : ℕ} (e : Fin w → Fin w') (b : Box Φ w)
    (x : Fin w' → Bool) : (embedBox e b).bits x = b.bits (x ∘ e) := rfl

private theorem tensor_congr_box {Φ : Type} (expI : Φ → ℂ) {w : ℕ} {b b' : Box Φ w}
    (h : b = b') (x : Fin w → Bool) :
    Label.tensor expI b.label (b.bits x) = Label.tensor expI b'.label (b'.bits x) := by
  subst h; rfl

/-- The box product of a juxtaposition splits into the two halves'. -/
private theorem prod_appendBoxes {Φ : Type} (expI : Φ → ℂ) {w₁ w₂ b₁ b₂ : ℕ}
    (A : Fin b₁ → Box Φ w₁) (B : Fin b₂ → Box Φ w₂)
    (x₁ : Fin w₁ → Bool) (x₂ : Fin w₂ → Bool) :
    (∏ i : Fin (b₁ + b₂), Label.tensor expI (appendBoxes A B i).label
        ((appendBoxes A B i).bits (Fin.addCases x₁ x₂)))
      = (∏ i, Label.tensor expI (A i).label ((A i).bits x₁))
        * ∏ i, Label.tensor expI (B i).label ((B i).bits x₂) := by
  have hl : (Fin.addCases x₁ x₂ : Fin (w₁ + w₂) → Bool) ∘ Fin.castAdd w₂ = x₁ :=
    funext fun k => by simp
  have hr : (Fin.addCases x₁ x₂ : Fin (w₁ + w₂) → Bool) ∘ Fin.natAdd w₁ = x₂ :=
    funext fun k => by simp
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    refine (tensor_congr_box expI (appendBoxes_left A B i) _).trans ?_
    rw [bits_embedBox, hl]
    rfl
  · refine Finset.prod_congr rfl fun i _ => ?_
    refine (tensor_congr_box expI (appendBoxes_right A B i) _).trans ?_
    rw [bits_embedBox, hr]
    rfl

private def appendIds {w₁ w₂ k₁ k₂ : ℕ}
    (A : Fin k₁ → Fin w₁ × Fin w₁) (B : Fin k₂ → Fin w₂ × Fin w₂) :
    Fin (k₁ + k₂) → Fin (w₁ + w₂) × Fin (w₁ + w₂) :=
  Fin.addCases (fun i => embedId (Fin.castAdd w₂) (A i))
               (fun i => embedId (Fin.natAdd w₁) (B i))

@[simp] private theorem appendIds_left {w₁ w₂ k₁ k₂ : ℕ}
    (A : Fin k₁ → Fin w₁ × Fin w₁) (B : Fin k₂ → Fin w₂ × Fin w₂) (i : Fin k₁) :
    appendIds A B (Fin.castAdd k₂ i) = embedId (Fin.castAdd w₂) (A i) := by
  simp [appendIds]

@[simp] private theorem appendIds_right {w₁ w₂ k₁ k₂ : ℕ}
    (A : Fin k₁ → Fin w₁ × Fin w₁) (B : Fin k₂ → Fin w₂ × Fin w₂) (i : Fin k₂) :
    appendIds A B (Fin.natAdd k₁ i) = embedId (Fin.natAdd w₁) (B i) := by
  simp [appendIds]

/-- The hypergraph of an algebraic term. -/
def ZX.toHyp : {n m : ℕ} → ZX n m → Hyp AlgPhase n m
  | _, _, .empty =>
      { wires := 0, boxCount := 0, boxes := Fin.elim0, idCount := 0, ids := Fin.elim0,
        inputs := Fin.elim0, outputs := Fin.elim0 }
  | _, _, .wire =>
      { wires := 1, boxCount := 0, boxes := Fin.elim0, idCount := 0, ids := Fin.elim0,
        inputs := fun _ => 0, outputs := fun _ => 0 }
  | _, _, .hadamard =>
      { wires := 2,
        boxCount := 1, boxes := fun _ => { label := .hadamard, arity := 2, legs := id },
        idCount := 0, ids := Fin.elim0,
        inputs := fun _ => 0, outputs := fun _ => 1 }
  | n, m, .spider c _ _ φ =>
      { wires := n + m,
        boxCount := 1,
        boxes := fun _ => { label := .spider c.toHypColour φ, arity := n + m, legs := id },
        idCount := 0, ids := Fin.elim0,
        inputs := Fin.castAdd m, outputs := Fin.natAdd n }
  | _, _, .stack a b =>
      let A := a.toHyp
      let B := b.toHyp
      { wires := A.wires + B.wires,
        boxCount := A.boxCount + B.boxCount,
        boxes := appendBoxes A.boxes B.boxes,
        idCount := A.idCount + B.idCount,
        ids := appendIds A.ids B.ids,
        inputs := Fin.addCases (fun i => Fin.castAdd B.wires (A.inputs i))
                               (fun i => Fin.natAdd A.wires (B.inputs i)),
        outputs := Fin.addCases (fun j => Fin.castAdd B.wires (A.outputs j))
                                (fun j => Fin.natAdd A.wires (B.outputs j)) }
  | _, _, .compose (m := m) a b =>
      let A := a.toHyp
      let B := b.toHyp
      { wires := A.wires + B.wires,
        boxCount := A.boxCount + B.boxCount,
        boxes := appendBoxes A.boxes B.boxes,
        idCount := A.idCount + B.idCount + m,
        ids := Fin.addCases (appendIds A.ids B.ids)
                 (fun i : Fin m =>
                    (Fin.castAdd B.wires (A.outputs i), Fin.natAdd A.wires (B.inputs i))),
        inputs := fun i => Fin.castAdd B.wires (A.inputs i),
        outputs := fun j => Fin.natAdd A.wires (B.outputs j) }

/-! ## Splitting an assignment

`stack` and `compose` both build their wires as `Fin (A.wires + B.wires)`, so
every proof about them has to take an assignment apart into the two halves and
put it back. These are generic facts about `Fin.addCases`, kept here because
this is the only file that needs them. -/

/-- A property of every `Fin (n + p)` is one of each half. -/
private theorem forall_fin_add {n p : ℕ} (P : Fin (n + p) → Prop) :
    (∀ i, P i) ↔ (∀ i : Fin n, P (Fin.castAdd p i)) ∧ (∀ j : Fin p, P (Fin.natAdd n j)) := by
  constructor
  · intro h
    exact ⟨fun i => h _, fun j => h _⟩
  · rintro ⟨h₁, h₂⟩ i
    induction i using Fin.addCases
    · exact h₁ _
    · exact h₂ _

/-- A `0`/`1` indicator of a conjunction splits into a product. Both `stack`
and `compose` need this to factor a summand into its two halves. -/
private theorem ite_and_mul {P Q : Prop} [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1 : ℂ) else 0) = (if P then 1 else 0) * (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- An assignment to `Fin (w₁ + w₂)` is a pair of assignments. -/
private def addCasesEquiv (w₁ w₂ : ℕ) :
    ((Fin w₁ → Bool) × (Fin w₂ → Bool)) ≃ (Fin (w₁ + w₂) → Bool) where
  toFun p := Fin.addCases p.1 p.2
  invFun a := (fun i => a (Fin.castAdd w₂ i), fun i => a (Fin.natAdd w₁ i))
  left_inv p := by ext i <;> simp
  right_inv a := by
    funext i
    induction i using Fin.addCases <;> simp

/-- A sum over assignments to `Fin (w₁ + w₂)` is a double sum over the halves. -/
private theorem sum_addCases {M : Type*} [AddCommMonoid M] {w₁ w₂ : ℕ}
    (F : (Fin (w₁ + w₂) → Bool) → M) :
    ∑ a : Fin (w₁ + w₂) → Bool, F a
      = ∑ a₁ : Fin w₁ → Bool, ∑ a₂ : Fin w₂ → Bool, F (Fin.addCases a₁ a₂) := by
  rw [← (addCasesEquiv w₁ w₂).sum_comp F, Fintype.sum_prod_type]
  rfl

/-! ## Phase 0 targets

Three instances of `sem_toHyp`, chosen to exercise each part of the encoding
before the general theorem is attempted: a bare wire (a vertex pinned twice by
the boundary), a spider (the box tensor and its leg list), and `wire ≫ wire`
(the smallest term where composition merges a wire at all — the case that
catches a merge which leaves a wire summed over freely). -/

theorem sem_toHyp_wire (f g : Wires 1) :
    (ZX.wire.toHyp).sem AlgPhase.expI f g = ZX.wire.sem f g := by
  simp only [ZX.toHyp, Hyp.sem, ZX.sem, Hyp.Sat, Finset.univ_eq_empty, Finset.prod_empty,
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

/-- A hypergraph's Z tensor on a merged boundary is the algebraic one on the
split boundary. -/
private theorem zTensor_addCases (φ : AlgPhase) {n m : ℕ} (f : Wires n) (g : Wires m) :
    zTensor AlgPhase.expI φ (Fin.addCases f g) = zSpiderSem φ f g := by
  simp only [zTensor, zSpiderSem, addCases_forall_eq]

/-- The two-leg Hadamard tensor is one entry of the Hadamard matrix. -/
private theorem hadTensor_pair (a b : Bool) : hadTensor ![a, b] = hadSem a b := by
  cases a <;> cases b <;> simp [hadTensor, hadSem] <;> decide +kernel

/-- Likewise for X, which both sides define by conjugating Z with Hadamards —
so this is that definition on either side of the lowering, and the work is
splitting the conjugating product and the summed-over boundary in two. -/
private theorem xTensor_addCases (φ : AlgPhase) {n m : ℕ} (f : Wires n) (g : Wires m) :
    xTensor AlgPhase.expI φ (Fin.addCases f g) = xSpiderSem φ f g := by
  rw [xTensor, sum_addCases]
  refine Finset.sum_congr rfl fun f' _ => Finset.sum_congr rfl fun g' _ => ?_
  rw [zTensor_addCases, Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, hadTensor_pair]
  have hswap : ∀ j, hadSem (g j) (g' j) = hadSem (g' j) (g j) := fun j => by
    simp only [hadSem, Bool.and_comm]
  simp only [hswap]
  ring

theorem sem_toHyp_spider (c : AlgSpColor) (n m : ℕ) (φ : AlgPhase) (f : Wires n) (g : Wires m) :
    ((ZX.spider c n m φ).toHyp).sem AlgPhase.expI f g = (ZX.spider c n m φ).sem f g := by
  simp only [ZX.toHyp, Hyp.sem, Hyp.Sat, IsEmpty.forall_iff, if_true, mul_one]
  rw [Finset.sum_eq_single (Fin.addCases f g)]
  · simp only [Label.tensor, Box.bits, id_eq, Fin.addCases_left, Fin.addCases_right,
      implies_true, and_self, if_true, one_mul, Fin.prod_univ_one]
    cases c with
    | Z => exact zTensor_addCases φ f g
    | X => exact xTensor_addCases φ f g
  · intro a _ hne
    have : ¬ ((∀ i, a (Fin.castAdd m i) = f i) ∧ (∀ j, a (Fin.natAdd n j) = g j)) := by
      rintro ⟨h₁, h₂⟩
      exact hne (funext fun i => by induction i using Fin.addCases <;> simp [h₁, h₂])
    simp [this]
  · simp

theorem sem_toHyp_wire_compose (f g : Wires 1) :
    ((ZX.wire ≫ ZX.wire).toHyp).sem AlgPhase.expI f g = (ZX.wire ≫ ZX.wire).sem f g := by
  simp only [ZX.toHyp, Hyp.sem, ZX.sem, Hyp.Sat, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
    Fin.forall_fin_one, Fin.addCases, embedId]
  rw [sum_wires2, sum_wires1]
  cases hf : f 0 <;> cases hg : g 0 <;> simp [zeroAmpl, oneAmpl]

/-! ## Stack

The two halves share no wires, so the sum over assignments factors into a sum
over each — which is `sum_addCases` — and every other part of the summand
factors with it: the boundary conditions by `forall_fin_add`, the
identifications likewise, and the box product by `Fin.prod_univ_add`. -/

theorem sem_toHyp_stack {n m p q : ℕ} (a : ZX n m) (b : ZX p q)
    (ihA : ∀ f g, (a.toHyp).sem AlgPhase.expI f g = a.sem f g)
    (ihB : ∀ f g, (b.toHyp).sem AlgPhase.expI f g = b.sem f g)
    (f : Wires (n + p)) (g : Wires (m + q)) :
    ((a ⊗ b).toHyp).sem AlgPhase.expI f g = (a ⊗ b).sem f g := by
  rw [ZX.sem, ← ihA, ← ihB]
  simp only [Hyp.sem]
  rw [ZX.toHyp, sum_addCases, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun xA _ => Finset.sum_congr rfl fun xB _ => ?_
  rw [prod_appendBoxes]
  simp only [appendIds_left, appendIds_right, Fin.addCases_left, Fin.addCases_right, embedId,
    Hyp.Sat, forall_fin_add]
  simp only [and_and_and_comm, ite_and_mul]
  ring

end SpLean.Algebraic
