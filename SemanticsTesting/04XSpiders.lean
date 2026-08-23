-- import SemanticsTesting.«03ZSpiders»

-- open SpLean.Algebraic

-- namespace SemanticsTesting

-- /--
--   Pending: X spiders, `hadamard` and `compose` (pqs 3.1.5)

--   Every goal below is currently *false*, because `ZX.sem` returns `0` on those
--   three branches. They are the pending obligations that fixing `sem` has to
--   discharge — leave the `sorry`s until then.
-- -/

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
