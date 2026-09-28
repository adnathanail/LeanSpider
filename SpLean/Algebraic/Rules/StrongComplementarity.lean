import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Rules.Lemmas
-- import SpLean.Panel

namespace SpLean.Algebraic

def strongCompLHS : ZX 2 2 := .spider .X 2 1 ≫ .spider .Z 1 2
-- #zx strongCompLHS

def strongCompRHS : ZX 2 2 := (.spider .Z 1 2 ⊗ .spider .Z 1 2 : ZX 2 4) ≫ (.wire ⊗ .swap ⊗ .wire : ZX 4 4) ≫ (.spider .X 2 1 ⊗ .spider .X 2 1)
-- #zx strongCompRHS

noncomputable abbrev strongCompScalar (n m : ℕ) : Complex := Real.sqrt 2 ^ ((n - 1) * (m - 1))

lemma strongCompScalar_ne_zero (n m : ℕ) :
    strongCompScalar n m ≠ 0 := by
  unfold strongCompScalar
  norm_num

lemma xSpiderSem_two_one (f : Wires 2) (g : Wires 1) :
    xSpiderSem (0 : AlgPhase) f g =
      if xor (f 0) (f 1) = g 0 then ((√2:ℝ):ℂ)⁻¹ else 0 := by
  simp only [xSpiderSem, sum_wires2, sum_wires1, zSpiderSem, hadSem, AlgPhase.expI_zero,
    Fin.prod_univ_two, Fin.prod_univ_one]
  cases f 0 <;> cases f 1 <;> cases g 0 <;>
    simp <;>
    norm_num [inv_root_two_mul_self_complex, inv_root_two_add_self_complex] <;>
    ring

lemma stackZ_sem (f : Wires 2) (c : Wires 4) :
    (ZX.spider .Z 1 2 (0 : AlgPhase) ⊗ ZX.spider .Z 1 2 (0 : AlgPhase)).sem f c =
      if c 0 = f 0 ∧ c 1 = f 0 ∧ c 2 = f 1 ∧ c 3 = f 1 then 1 else 0 := by
  have e1 : (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 := rfl
  have e2 : (Fin.natAdd 1 (0 : Fin 1) : Fin 2) = 1 := rfl
  have e3 : (Fin.castAdd 2 (0 : Fin 2) : Fin 4) = 0 := rfl
  have e4 : (Fin.castAdd 2 (1 : Fin 2) : Fin 4) = 1 := rfl
  have e5 : (Fin.natAdd 2 (0 : Fin 2) : Fin 4) = 2 := rfl
  have e6 : (Fin.natAdd 2 (1 : Fin 2) : Fin 4) = 3 := rfl
  simp only [ZX.sem, zSpiderSem, AlgPhase.expI_zero, Fin.forall_fin_one, Fin.forall_fin_two,
    e1, e2, e3, e4, e5, e6]
  cases f 0 <;> cases f 1 <;> cases c 0 <;> cases c 1 <;> cases c 2 <;> cases c 3 <;> simp_all

lemma wireSwapWire_sem (c d : Wires 4) :
    (ZX.wire ⊗ ZX.swap ⊗ ZX.wire : ZX 4 4).sem c d =
      if d 0 = c 0 ∧ d 1 = c 2 ∧ d 2 = c 1 ∧ d 3 = c 3 then 1 else 0 := by
  have e1 : (Fin.castAdd 3 (0 : Fin 1) : Fin 4) = 0 := rfl
  have e2 : (Fin.natAdd 1 (Fin.castAdd 1 (0 : Fin 2)) : Fin 4) = 1 := rfl
  have e3 : (Fin.natAdd 1 (Fin.castAdd 1 (1 : Fin 2)) : Fin 4) = 2 := rfl
  have e4 : (Fin.natAdd 1 (Fin.natAdd 2 (0 : Fin 1)) : Fin 4) = 3 := rfl
  simp only [ZX.sem, e1, e2, e3, e4]
  split_ifs <;> simp_all

lemma stackX_sem (d : Wires 4) (g : Wires 2) :
    (ZX.spider .X 2 1 (0 : AlgPhase) ⊗ ZX.spider .X 2 1 (0 : AlgPhase)).sem d g =
      (if xor (d 0) (d 1) = g 0 then ((√2:ℝ):ℂ)⁻¹ else 0) *
      (if xor (d 2) (d 3) = g 1 then ((√2:ℝ):ℂ)⁻¹ else 0) := by
  have e1 : (Fin.castAdd 2 (0 : Fin 2) : Fin 4) = 0 := rfl
  have e2 : (Fin.castAdd 2 (1 : Fin 2) : Fin 4) = 1 := rfl
  have e3 : (Fin.natAdd 2 (0 : Fin 2) : Fin 4) = 2 := rfl
  have e4 : (Fin.natAdd 2 (1 : Fin 2) : Fin 4) = 3 := rfl
  have e5 : (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 := rfl
  have e6 : (Fin.natAdd 1 (0 : Fin 1) : Fin 2) = 1 := rfl
  simp only [ZX.sem, e1, e2, e3, e4, e5, e6, xSpiderSem_two_one]

lemma sum_wires4_delta {M : Type*} [AddCommMonoid M] (p : Wires 4) (F : Wires 4 → M) :
    ∑ c : Wires 4, (if c 0 = p 0 ∧ c 1 = p 1 ∧ c 2 = p 2 ∧ c 3 = p 3 then F c else 0) = F p := by
  have hiff : ∀ c : Wires 4, (c 0 = p 0 ∧ c 1 = p 1 ∧ c 2 = p 2 ∧ c 3 = p 3) ↔ c = p := by
    intro c
    constructor
    · rintro ⟨h0, h1, h2, h3⟩
      funext i
      fin_cases i <;> assumption
    · rintro rfl
      exact ⟨rfl, rfl, rfl, rfl⟩
  simp only [hiff, Finset.sum_ite_eq']
  exact if_pos (Finset.mem_univ p)

lemma sum_wires4_delta' {M : Type*} [AddCommMonoid M] (a b c d : Bool) (F : Wires 4 → M) :
    ∑ x : Wires 4, (if x 0 = a ∧ x 1 = b ∧ x 2 = c ∧ x 3 = d then F x else 0)
      = F ![a, b, c, d] := by
  have h := sum_wires4_delta (M := M) (p := ![a, b, c, d]) F
  simpa using h

theorem strong_complementarity_2 :
    strongCompLHS ≈zx strongCompRHS := by
  unfold strongCompLHS strongCompRHS
  refine ⟨strongCompScalar 2 2, strongCompScalar_ne_zero 2 2, fun f g => ?_⟩
  change
      (∑ h : Wires 1, xSpiderSem (0 : AlgPhase) f h * zSpiderSem (0 : AlgPhase) h g)
      = strongCompScalar 2 2 * ∑ c : Wires 4,
          (ZX.spider .Z 1 2 (0 : AlgPhase) ⊗ ZX.spider .Z 1 2 (0 : AlgPhase)).sem f c *
            ∑ d : Wires 4, (ZX.wire ⊗ ZX.swap ⊗ ZX.wire : ZX 4 4).sem c d *
              (ZX.spider .X 2 1 (0 : AlgPhase) ⊗ ZX.spider .X 2 1 (0 : AlgPhase)).sem d g
  simp only [xSpiderSem_two_one, zSpiderSem, AlgPhase.expI_zero, stackZ_sem, wireSwapWire_sem,
    stackX_sem, ite_mul, one_mul, zero_mul, sum_wires4_delta', sum_wires1]
  simp only [strongCompScalar]
  norm_num
  cases f 0 <;> cases f 1 <;> cases g 0 <;> cases g 1 <;> simp_all

end SpLean.Algebraic
