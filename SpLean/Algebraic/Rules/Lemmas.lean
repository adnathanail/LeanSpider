import SpLean.Algebraic.Semantics

namespace SpLean.Algebraic

-- Boundary assignments of a single wire. `abbrev`, not `def`, so `simp` and
-- `norm_num` can still see through to `false`/`true`.
abbrev zeroAmpl : Wires 1 := fun _ => false
abbrev oneAmpl : Wires 1 := fun _ => true

/-- A sum over every single-wire boundary assignment is a two-term sum: there
are only `zeroAmpl` and `oneAmpl`. Replaces the
`rw [show Finset.univ = {zeroAmpl, oneAmpl} from by decide]; rw [Finset.sum_pair (by decide)]`
pair; use `simp only [sum_wires1]` to hit nested sums in one go. -/
lemma sum_wires1 {M : Type*} [AddCommMonoid M] (F : Wires 1 → M) :
    ∑ g : Wires 1, F g = F zeroAmpl + F oneAmpl := by
  rw [show (Finset.univ : Finset (Wires 1)) = {zeroAmpl, oneAmpl} from by decide]
  exact Finset.sum_pair (by decide)

lemma sum_wires2 {M : Type*} [AddCommMonoid M] (F : Wires 2 → M) :
    ∑ x : Wires 2, F x = ∑ a : Bool, ∑ b : Bool, F ![a, b] := by
  rw [← Equiv.sum_comp
    (⟨fun p => ![p.1, p.2], fun x => (x 0, x 1), by decide, by decide⟩ :
      Bool × Bool ≃ Wires 2) F]
  simp [Fintype.sum_prod_type]

lemma sum_wires3 {M : Type*} [AddCommMonoid M] (F : Wires 3 → M) :
    ∑ x : Wires 3, F x = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, F ![a, b, c] := by
  rw [← Equiv.sum_comp
    (⟨fun p => ![p.1, p.2.1, p.2.2], fun x => (x 0, x 1, x 2), by decide, by decide⟩ :
      Bool × Bool × Bool ≃ Wires 3) F]
  simp [Fintype.sum_prod_type]

/-- A sum over an `m + k`-wire boundary splits into a sum over its first `m`
wires and a sum over its last `k` — the sum-side counterpart to how `stack`
splits a boundary with `Fin.castAdd`/`Fin.natAdd`. -/
lemma sum_wires_append {M : Type*} [AddCommMonoid M] {m k : ℕ} (F : Wires (m + k) → M) :
    ∑ g : Wires (m + k), F g = ∑ p : Wires m, ∑ q : Wires k, F (Fin.append p q) := by
  rw [← Equiv.sum_comp (Fin.appendEquiv m k) F, Fintype.sum_prod_type]
  rfl

lemma prod_wires1 {M : Type*} [CommMonoid M] (F : Wires 1 → M) :
    ∏ g : Wires 1, F g = F zeroAmpl * F oneAmpl := by
  rw [show (Finset.univ : Finset (Wires 1)) = {zeroAmpl, oneAmpl} from by decide]
  exact Finset.prod_pair (by decide)

/-- A single-wire boundary assignment is determined by its one bit. -/
lemma wires1_eq_of_head {f g : Wires 1} (h : f 0 = g 0) : f = g :=
  funext fun i => by rw [Fin.fin_one_eq_zero i, h]

/-- A single-wire boundary assignment is the constant function at its one bit. -/
lemma wires1_eq_const (g : Wires 1) : g = fun _ => g 0 :=
  funext fun i => by rw [Fin.fin_one_eq_zero i]

/-- Boundary assignments for wires where all are false -/
lemma all_wires_false {n : ℕ} :
  ∀ x : Fin n → Bool, (∀ i, x i = false) ↔ x = fun _ => false := by
  exact fun x => Iff.symm funext_iff
/-- Boundary assignments for wires where all are true -/
lemma all_wires_true {n : ℕ} :
  ∀ x : Fin n → Bool, (∀ i, x i = true) ↔ x = fun _ => true := by
  exact fun x => Iff.symm funext_iff

lemma sum_bool_all_false {n : ℕ} {M : Type*} [AddCommMonoid M]
    (a : (Fin n → Bool) → M) :
    ∑ x : Fin n → Bool,
        (if ∀ i, x i = false then a x else 0) = a (fun _ => false) := by
  simp only [all_wires_false]
  norm_num

lemma sum_bool_all_true {n : ℕ} {M : Type*} [AddCommMonoid M]
    (a : (Fin n → Bool) → M) :
    ∑ x : Fin n → Bool,
        (if ∀ i, x i = true then a x else 0) = a (fun _ => true) := by
  simp only [all_wires_true]
  norm_num

/-- Both endpoints at once. Just the two one-sided lemmas, split apart with
`Finset.sum_add_distrib`. -/
lemma sum_bool_endpoints {n : ℕ} {M : Type*} [AddCommMonoid M]
    (a b : (Fin n → Bool) → M) :
    ∑ x : Fin n → Bool,
        ((if ∀ i, x i = false then a x else 0) + if ∀ i, x i = true then b x else 0)
      = a (fun _ => false) + b (fun _ => true) := by
  rw [Finset.sum_add_distrib, sum_bool_all_false, sum_bool_all_true]

/-- The two-boundary version of `sum_bool_endpoints`: a double sum whose only
surviving terms are "everything false" and "everything true" on *both*
boundaries at once. This is the shape the RHS of a spider-fusion goal takes,
where the `∀ i, x i = false` and `∀ j, y j = false` guards are conjoined
inside a single `ite`. -/
lemma sum_bool_endpoints₂ {n m : ℕ} {M : Type*} [AddCommMonoid M]
    (a b : (Fin n → Bool) → (Fin m → Bool) → M) :
    ∑ x : Fin n → Bool, ∑ y : Fin m → Bool,
        ((if (∀ i, x i = false) ∧ (∀ j, y j = false) then a x y else 0)
          + if (∀ i, x i = true) ∧ (∀ j, y j = true) then b x y else 0)
      = a (fun _ => false) (fun _ => false) + b (fun _ => true) (fun _ => true) := by
  simp only [all_wires_false, all_wires_true, ite_and, Finset.sum_add_distrib]
  simp

/-! ### Splitting a boundary in two

`stack` and `compose` build their boundaries as `Fin (n + p)`, so proofs about
them take an assignment apart into two halves and put it back. These are
generic facts about `Fin.addCases`, used both by the rules in `Rules/` and by
the hypergraph lowering in `Algebraic/ToHypergraph.lean`. -/

/-- A property of every `Fin (n + p)` is one of each half. -/
theorem forall_fin_add {n p : ℕ} (P : Fin (n + p) → Prop) :
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
theorem ite_and_mul {P Q : Prop} [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1 : ℂ) else 0) = (if P then 1 else 0) * (if Q then 1 else 0) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- An assignment to `Fin (w₁ + w₂)` is a pair of assignments. -/
def addCasesEquiv (w₁ w₂ : ℕ) :
    ((Fin w₁ → Bool) × (Fin w₂ → Bool)) ≃ (Fin (w₁ + w₂) → Bool) where
  toFun p := Fin.addCases p.1 p.2
  invFun a := (fun i => a (Fin.castAdd w₂ i), fun i => a (Fin.natAdd w₁ i))
  left_inv p := by ext i <;> simp
  right_inv a := by
    funext i
    induction i using Fin.addCases <;> simp

/-- A sum over assignments to `Fin (w₁ + w₂)` is a double sum over the halves. -/
theorem sum_addCases {M : Type*} [AddCommMonoid M] {w₁ w₂ : ℕ}
    (F : (Fin (w₁ + w₂) → Bool) → M) :
    ∑ a : Fin (w₁ + w₂) → Bool, F a
      = ∑ a₁ : Fin w₁ → Bool, ∑ a₂ : Fin w₂ → Bool, F (Fin.addCases a₁ a₂) := by
  rw [← (addCasesEquiv w₁ w₂).sum_comp F, Fintype.sum_prod_type]
  rfl


/-! ### `√2` arithmetic -/

lemma inv_root_two_add_self : (√2)⁻¹ + (√2)⁻¹ = √2 := by
  field_simp
  norm_num
lemma inv_root_two_add_self_complex :
    ((√2 : ℝ) : ℂ)⁻¹ + ((√2 : ℝ) : ℂ)⁻¹ = √2 := by
  norm_cast
  rw [inv_root_two_add_self]

lemma inv_root_two_mul_self : (√2)⁻¹ * (√2)⁻¹ = 1/2 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num
lemma inv_root_two_mul_self_complex :
    ((√2 : ℝ) : ℂ)⁻¹ * ((√2 : ℝ) : ℂ)⁻¹ = 1/2 := by
  norm_cast
  rw [inv_root_two_mul_self]
  norm_num

lemma inv_root_two_sq : (√2)⁻¹ ^ 2 = 1/2 := by
  rw [sq, inv_root_two_mul_self]
lemma inv_root_two_sq_complex : ((√2 : ℝ) : ℂ)⁻¹ ^ 2 = 1/2 := by
  rw [sq, inv_root_two_mul_self_complex]

theorem inv_root_two_eq_div : ((√2 : ℝ))⁻¹ = √2 / 2 := by
  rw [eq_div_iff (by norm_num : (2:ℝ) ≠ 0), inv_mul_eq_div,
    div_eq_iff (Real.sqrt_ne_zero'.2 (by norm_num))]
  exact (Real.mul_self_sqrt (by norm_num)).symm

/-!
# X gate semantics
-/

lemma x_gate_xSpiderSem_entries (f g : Wires 1) :
    xSpiderSem π f g = if f 0 = g 0 then 0 else 1 := by
  simp only [xSpiderSem, sum_wires1, zSpiderSem, hadSem]
  cases hf : f 0 <;> cases hg : g 0 <;>
    norm_num [hf, hg, inv_root_two_mul_self_complex]

-- Copied from SemanticsTesting.06Compose.lean
lemma x_gate_sem (f g : Wires 1) :
    (ZX.spider .X 1 1 π).sem f g = if f 0 = g 0 then 0 else 1 := by
  rw [ZX.sem, x_gate_xSpiderSem_entries]

end SpLean.Algebraic
