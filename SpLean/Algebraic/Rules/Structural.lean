import SpLean.Algebraic.ZX
import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Rules.Lemmas
import SpLean.Algebraic.Combinators
import SpLean.Algebraic.Tactics

namespace SpLean.Algebraic

/-!
# Combinator semantics
-/

theorem nStack_sem (k : ℕ) (d : ZX 1 1) (u v : Wires k) :
    (ZX.nStack k d).sem u v = ∏ j, d.sem (fun _ => u j) (fun _ => v j) := by
  induction k with
  | zero =>
    simp only [ZX.nStack, ZX.sem]
    trivial
  | succ k ih =>
    simp only [ZX.nStack]
    rw [ZX.sem]
    rw [ih]
    have hlast : ∀ i : Fin 1, Fin.natAdd k i = Fin.last k := by
      intro i
      rw [Subsingleton.elim i 0]
      rfl
    rw [Fin.prod_univ_castSucc (f := fun j => d.sem (fun _ => u j) (fun _ => v j))]
    simp only [hlast, Fin.castSucc]

theorem nWire_sem (k : ℕ) (u v : Wires k) :
    (ZX.nWire k).sem u v = if u = v then 1 else 0 := by
  induction k with
  | zero =>
    simp only [ZX.nWire, ZX.nStack, ZX.sem]
    trivial
  | succ k ih =>
    simp only [ZX.nWire, ZX.nStack, ZX.sem]
    rw [ih]
    simp only [Fin.isValue, mul_ite, mul_one, mul_zero]
    rw [← ite_and]
    refine if_congr ?_ rfl rfl
    rw [funext_iff, funext_iff]
    rw [Fin.forall_fin_succ', and_comm]
    rfl

theorem nHadamard_sem (k : ℕ) (u v : Wires k) :
    (ZX.nHadamard k).sem u v = ∏ i, hadSem (u i) (v i) := by
  rw [nStack_sem]
  simp only [ZX.sem]

theorem nStack_pi_sem (k : ℕ) (u v : Wires k) :
    (ZX.nStack k (ZX.spider .X 1 1 π)).sem u v = ∏ i : Fin k, xSpiderSem π ((fun _ => u i) : Wires 1) ((fun _ => v i) : Wires 1) := by
  rw [nStack_sem]
  simp only [ZX.sem]

theorem nStackState_sem (k : ℕ) (d : ZX 0 1) (u : Wires 0) (v : Wires k) :
    (ZX.nStackState k d).sem u v = ∏ j, d.sem u (fun _ => v j) := by
  induction k with
  | zero =>
    simp only [ZX.nStackState, ZX.sem]
    trivial
  | succ k ih =>
    simp only [ZX.nStackState]
    rw [ZX.sem]
    have hu :
      (fun i => u (Fin.castAdd 0 i)) = u := by trivial
    rw [hu, ih]
    have hu' :
      (fun i => u (Fin.natAdd 0 i)) = u := by norm_num
    rw [hu']
    rw [Fin.prod_univ_castSucc (f := fun j => d.sem u (fun _ => v j))]
    have hcastSucc :
      ∀ i : Fin k, i.castSucc = Fin.castAdd 1 i := by exact fun i => Fin.eq_of_val_eq rfl
    have hlastk :
      ∀ j : Fin 1, Fin.natAdd k j = Fin.last k := by grind
    simp only [hcastSucc, hlastk]

/-!
# Structural laws for `≫`

`(a ≫ b) ≫ c` and `a ≫ (b ≫ c)` are different terms, with the same semantics

`compose_assoc` allows regrouping a diagram so the rule can see its redex:
  `hadamard ≫ (hadamard ≫ c)` has no `hadamard ≫ hadamard` subterm for
    `hadamard_hadamard` to hit until it is reassociated.

`wire_compose`/`compose_wire` then clear away the `wire` such a cancellation
leaves behind.
-/

/-- Composition is associative up to `≈zx`.

Use it with `zx_rw` to regroup before another rule fires; the arguments are
explicit so a particular grouping can be targeted:
`zx_rw [← compose_assoc ZX.hadamard ZX.hadamard]`. -/
theorem compose_assoc {n m k l : ℕ} (a : ZX n m) (b : ZX m k) (c : ZX k l) :
    ((a ≫ b) ≫ c) ≈zx (a ≫ (b ≫ c)) := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- A `wire` on the left of a composition does nothing. -/
theorem wire_compose {m : ℕ} (a : ZX 1 m) : (ZX.wire ≫ a) ≈zx a := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem]
  rw [sum_wires1]
  cases h : f 0 <;> simp
  · rw [wires1_eq_of_head (g := zeroAmpl) h]
  · rw [wires1_eq_of_head (g := oneAmpl) h]

/-- A `wire` on the right of a composition does nothing. -/
theorem compose_wire {n : ℕ} (a : ZX n 1) : (a ≫ ZX.wire) ≈zx a := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem]
  rw [sum_wires1]
  cases h : g 0 <;> simp
  · rw [wires1_eq_of_head (g := zeroAmpl) h]
  · rw [wires1_eq_of_head (g := oneAmpl) h]

/-- `nWire n` is a left identity for `≫` — the `n`-wire form of `wire_compose`. -/
theorem nWire_compose {n m : ℕ} (a : ZX n m) : (ZX.nWire n ≫ a) ≈zx a := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, nWire_sem]
  have h : ∀ x : Wires n,
    (if f = x then 1 else 0) * a.sem x g = if f = x then a.sem f g else 0 := by
      simp_all only [ite_mul, one_mul, zero_mul, implies_true]
  simp only [h]
  norm_num

/-- `nWire m` is a right identity for `≫` — the `n`-wire form of `compose_wire`. -/
theorem compose_nWire {n m : ℕ} (a : ZX n m) : (a ≫ ZX.nWire m) ≈zx a := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, nWire_sem]
  have h : ∀ x : Wires m,
    (a.sem f x * if x = g then 1 else 0) = if x = g then a.sem f g else 0 := by
      simp_all only [mul_ite, mul_one, mul_zero, implies_true]
  simp only [h]
  norm_num

/-- The interchange law: composing two stacks is stacking the two compositions.
Lets a rule about `a ≫ b` fire when `a` and `b` each sit in a different layer
of a stack. -/
theorem stack_compose_interchange {n m k n' m' k' : ℕ}
    (a : ZX n m) (b : ZX m k) (c : ZX n' m') (d : ZX m' k') :
    ((a ⊗ c) ≫ (b ⊗ d)) ≈zx ((a ≫ b) ⊗ (c ≫ d)) := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  simp only [ZX.sem, one_mul, sum_wires_append, Fin.append_left, Fin.append_right,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- Stacking is associative up to `≈zx`;
the cast is needed because `(n + p) + r` and `n + (p + r)` are different arities -/
theorem stack_assoc {n m p q r s : ℕ} (a : ZX n m) (b : ZX p q) (c : ZX r s) :
    ZX.cast (Nat.add_assoc n p r) (Nat.add_assoc m q s) ((a ⊗ b) ⊗ c)
      ≈zx (a ⊗ (b ⊗ c)) := by
  have hll : ∀ {x y z : ℕ} (i : Fin x),
      Fin.cast (Nat.add_assoc x y z) (Fin.castAdd z (Fin.castAdd y i))
        = Fin.castAdd (y + z) i := by
    intro x y z i; apply Fin.ext; simp
  have hlr : ∀ {x y z : ℕ} (i : Fin y),
      Fin.cast (Nat.add_assoc x y z) (Fin.castAdd z (Fin.natAdd x i))
        = Fin.natAdd x (Fin.castAdd z i) := by
    intro x y z i; apply Fin.ext; simp
  have hr : ∀ {x y z : ℕ} (i : Fin z),
      Fin.cast (Nat.add_assoc x y z) (Fin.natAdd (x + y) i)
        = Fin.natAdd x (Fin.natAdd y i) := by
    intro x y z i; apply Fin.ext; simp [Nat.add_assoc]
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul, ZX.sem_cast]
  simp only [ZX.sem, mul_assoc, hll, hlr, hr]


/-- Stacking the empty diagram on the right does nothing. -/
theorem stack_empty {n m : ℕ} (a : ZX n m) : (a ⊗ .empty) ≈zx a := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, mul_one]
  congr 1

/-- Composing with the empty diagram after an effect does nothing. -/
theorem compose_empty {n : ℕ} (a : ZX n 0) : (a ≫ ZX.empty) ≈zx a := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  simp only [ZX.sem, mul_one, one_mul]
  exact Fintype.sum_subsingleton _ g

 /-- Stacking the empty diagram on the left does nothing either
  needs the cast because `0 + n` does not reduce. -/
theorem empty_stack {n m : ℕ} (a : ZX n m) :
    ZX.cast (Nat.zero_add n) (Nat.zero_add m) (.empty ⊗ a) ≈zx a := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul, ZX.sem_cast]
  simp only [ZX.sem, one_mul]
  congr 1 <;> funext i <;> congr 1 <;> (apply Fin.ext; simp)

/--
`empty_stack` with the cast on the other side,
  so `zx_rw` can fire it on an `ZX.empty ⊗ a` sitting inside a diagram.
The rewrite leaves a `ZX.cast` where the subterm was,
  which `ZX.cast_self` clears whenever the arities are concrete. -/
theorem empty_stack' {n m : ℕ} (a : ZX n m) :
    (ZX.empty ⊗ a) ≈zx ZX.cast (Nat.zero_add n).symm (Nat.zero_add m).symm a :=
  (ZX.Equiv.cast_iff _ _ _ _).mp (empty_stack a)

/-- Composing the empty diagram on the right does nothing. -/
theorem empty_compose_empty_eq_empty : (ZX.empty ≫ ZX.empty) ≈zx ZX.empty := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, mul_one]
  norm_num

theorem nStack_one (d : ZX 1 1) :
    (ZX.nStack 1 d) ≈zx d := by
  simp only [ZX.nStack]
  zx_rw [← ZX.cast_self _ _ (ZX.empty ⊗ d)]
  zx_rw [empty_stack]

theorem nStack_compose (k : ℕ) (a b : ZX 1 1) :
    (ZX.nStack k (a ≫ b) ≈zx (ZX.nStack k a) ≫ (ZX.nStack k b)) := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  have hsum1 : ∀ F : Wires 1 → ℂ, ∑ x : Wires 1, F x = ∑ c : Bool, F (fun _ => c) := by
    intro F
    rw [sum_wires1, Fintype.sum_bool]
    exact add_comm _ _
  simp only [nStack_sem, ZX.sem, hsum1, ← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]

theorem nStackState_compose_nStack (k : ℕ) (a : ZX 0 1) (b : ZX 1 1) :
    (ZX.nStackState k a ≫ ZX.nStack k b ≈zx (ZX.nStackState k (a ≫ b))) := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, nStack_sem, nStackState_sem]
  have hsum1 : ∀ F : Wires 1 → ℂ, ∑ x : Wires 1, F x = ∑ c : Bool, F (fun _ => c) := by
    intro F
    rw [sum_wires1, Fintype.sum_bool]
    exact add_comm _ _
  simp only [hsum1, ← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]

theorem nHadamard_one :
    (ZX.nHadamard 1) ≈zx ZX.hadamard := by
  rw [ZX.nHadamard]
  zx_rw [nStack_one]

/-- A layer of `k + l` Hadamards splits into a layer of `k` stacked on a layer of `l`. -/
theorem nHadamard_add (k l : ℕ) :
    ZX.nHadamard (k + l) ≈zx (ZX.nHadamard k ⊗ ZX.nHadamard l) := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  simp only [ZX.sem, nStack_sem, one_mul, Fin.prod_univ_add]

/-! ### Congruence for the `nStack` combinators

Allows `zx_rw` to work inside `nStack`
Tagged here rather than `Tactics.lean` to prevent circular import -/

@[gcongr]
theorem nStack_congr {k : ℕ} {a b : ZX 1 1} (h : a ≈zx b) :
    ZX.nStack k a ≈zx ZX.nStack k b := by
  induction k with
  | zero => rfl
  | succ k ih => exact ZX.Equiv.stack_congr ih h

@[gcongr]
theorem nStackState_congr {k : ℕ} {a b : ZX 0 1} (h : a ≈zx b) :
    ZX.nStackState k a ≈zx ZX.nStackState k b := by
  induction k with
  | zero => rfl
  | succ k ih => exact ZX.Equiv.stack_congr ih h

end SpLean.Algebraic
