import SpLean.Algebraic.Semantics

namespace SpLean.Algebraic

/-- Semantic equivalence of ZX terms: equal tensors up to a nonzero global
scalar (VyZX's proportionality). -/
-- TODO track scalar factors
def ZX.Equiv {n m : ℕ} (a b : ZX n m) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ ∀ f g, a.sem f g = c * b.sem f g

-- TODO should this be ≃?
@[inherit_doc] scoped infix:50 " ≈zx " => ZX.Equiv

namespace ZX.Equiv

@[refl] theorem refl {n m : ℕ} (a : ZX n m) : a ≈zx a := by
  use 1
  norm_num

@[symm] theorem symm {n m : ℕ} {a b : ZX n m} : a ≈zx b → b ≈zx a := by
  -- Expand a→b equivalence into existential
  rw [ZX.Equiv]
  -- Split implication into hypothesis and goal
  intro h
  -- Split up existential hypothesis
  obtain ⟨c, hc, hab⟩ := h
  -- Expand b→a equivalence
  rw [ZX.Equiv]
  -- Rewrite b→a to have the constant on RHS
  refine ⟨c⁻¹, inv_ne_zero hc, fun f g => ?_⟩
  rw [
    -- Use hypothesis to replace a.sem with b.sem
    hab f g,
    -- Simplify constants (using non-negativity hypothesis)
    inv_mul_cancel_left₀ hc
  ]

@[trans] theorem trans {n m : ℕ} {a b c : ZX n m} : a ≈zx b → b ≈zx c → a ≈zx c := by
  rintro ⟨c₁, hc₁, h₁⟩ ⟨c₂, hc₂, h₂⟩
  refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, fun f g => ?_⟩
  rw [h₁ f g, h₂ f g, mul_assoc]

instance {n m : ℕ} : Trans (α := ZX n m) ZX.Equiv ZX.Equiv ZX.Equiv := ⟨ZX.Equiv.trans⟩

/-- Equal denotations give equivalent diagrams (`c = 1`).
Escape hatch for when a diagram identity is not an instance of any rewrite rule. -/
theorem of_sem_eq {n m : ℕ} {a b : ZX n m} (h : a.sem = b.sem) : a ≈zx b :=
  ⟨1, one_ne_zero, fun f g => by rw [one_mul, h]⟩

/-- A spider's denotation depends on its phase only through `AlgPhase.expI`, so
phases equal *as angles* give equivalent spiders even when they differ as
rationals: `ZX.spider .Z 1 1 (2π)` and `ZX.spider .Z 1 1 0` are not the same
term, but they are the same diagram. This is the congruence that makes
`AlgPhase.equiv` rather than `=` the right notion of phase equality here.

Both colours go through it, because `xSpiderSem` is defined as `zSpiderSem`
conjugated by Hadamards and so mentions the phase in exactly one place. -/
theorem spider_congr (c : AlgSpColor) (n m : ℕ) {α β : AlgPhase}
    (h : AlgPhase.equiv α β) : ZX.spider c n m α ≈zx ZX.spider c n m β := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  cases c <;>
    simp only [ZX.sem, xSpiderSem, zSpiderSem, AlgPhase.expI_congr h]

/-! ### Congruence

To allow grw to do rewrites within a larger diagram, we have to provide congruence
  proofs for our composition operators
These are tagged with `@[gcongr]` in `SpLean/Algebraic/Tactics.lean`
  to keep the grw imports there. -/

theorem compose_congr {n m k : ℕ} {a a' : ZX n m} {b b' : ZX m k}
    (ha : a ≈zx a') (hb : b ≈zx b') : (a ≫ b) ≈zx (a' ≫ b') := by
  obtain ⟨c₁, hc₁, h₁⟩ := ha
  obtain ⟨c₂, hc₂, h₂⟩ := hb
  refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, fun f g => ?_⟩
  simp only [ZX.sem, h₁, h₂, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem stack_congr {n m p q : ℕ} {a a' : ZX n m} {b b' : ZX p q}
    (ha : a ≈zx a') (hb : b ≈zx b') : (a ⊗ b) ≈zx (a' ⊗ b') := by
  obtain ⟨c₁, hc₁, h₁⟩ := ha
  obtain ⟨c₂, hc₂, h₂⟩ := hb
  refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, fun f g => ?_⟩
  simp only [ZX.sem, h₁, h₂]
  ring

end ZX.Equiv

end SpLean.Algebraic
