import SemanticsTesting.Utils

open SpLean.Algebraic

/--
  # Z-basis states (pqs eq 3.6)
-/

-- ## 0 state
-- (X0)- = √2|0⟩ = |0⟩
abbrev zeroState : ZX 0 1 := .spider .X 0 1 ⟨0, 1⟩
#zx zeroState
theorem x_sem_zero_state (f : Wires 0) : zeroState.sem f = (![rootTwo, 0] : Fin 2 → ℂ) := by
  ext g
  rw [wiresVec1, ZX.sem, xSpiderSem, Phase.angle]
  have h0 : (Finset.univ : Finset (Wires 0)) = {λ _ => false} := by
    decide
  rw [h0, Finset.sum_singleton]
  have h1 : (Finset.univ : Finset (Wires 1)) = {λ _ => false, λ _ => true} := by
    decide
  have h_not_mem : (λ _ : Fin 1 => false) ∉ ({λ _ : Fin 1 => true} : Finset (Wires 1)) := by
    decide
  rw [h1, Finset.sum_insert h_not_mem, Finset.sum_singleton]
  simp [hadSem, zSpiderSem, Complex.exp_zero, rootTwo]
  have h_sqrt_add : ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) + ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) = (Real.sqrt 2 : ℂ) := by
    have h_sq : (Real.sqrt 2 : ℂ) ^ 2 = (2 : ℂ) := by
      norm_cast
      exact Real.sq_sqrt (show 0 ≤ 2 from by norm_num)
    have h_pos : (Real.sqrt 2 : ℂ) ≠ 0 := by
      intro hzero
      have : (Real.sqrt 2 : ℝ) = 0 := by exact_mod_cast hzero
      have hpos' : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : 0 < (2 : ℝ))
      linarith
    field_simp [h_pos]
    have h2 : (1 : ℂ) + 1 = (2 : ℂ) := by norm_num
    rw [h2]
    exact h_sq.symm
  cases g 0 with
  | false => norm_num [h_sqrt_add]
  | true => norm_num



-- -- |0⟩ (up to √2): the phaseless X spider 0 → 1, i.e. the vector (√2, 0).
-- abbrev zeroState : ZX 0 1 := .spider .X 0 1 ⟨0, 1⟩
-- #zx zeroState
-- theorem x_sem_zero_state_zero (f : Wires 0) :
--     zeroState.sem f zeroAmpl = rootTwo := by
--   sorry

-- theorem x_sem_zero_state_one (f : Wires 0) :
--     zeroState.sem f oneAmpl = 0 := by
--   sorry

-- -- H|+⟩ = |0⟩, scalar-exact: both sides are (√2, 0). This is the real test of
-- -- `hadamard`, since it turns the two equal amplitudes of |+⟩ into a cancellation.
-- abbrev plusThroughHadamard : ZX 0 1 := plusState × .hadamard
-- #zx plusThroughHadamard
-- theorem z_sem_hadamard_plus_state (f : Wires 0) (g : Wires 1) :
--     plusThroughHadamard.sem f g = zeroState.sem f g := by
--   sorry

-- -- ⟨−|+⟩ = 0: the plus state capped by a π-phase Z effect. Tests that `compose`
-- -- sums over the shared wire — a `compose` that dropped the sum cannot give 0.
-- abbrev plusMeetsMinus : ZX 0 0 := plusState × .spider .Z 1 0 ⟨1, 1⟩
-- #zx plusMeetsMinus
-- theorem z_sem_plus_minus_orthogonal (f g : Wires 0) :
--     plusMeetsMinus.sem f g = 0 := by
--   sorry

-- end SemanticsTesting
