import SemanticsTesting.Utils
import ProofWidgets.Component.Panel.SelectionPanel

open SpLean.Algebraic

/-!
# Exercise 3.7, algebraically

The diagram `exercise3point7` in `Main.lean`, as an algebraic term, rearranged
until its π phases sit on the output wires — `ex37_pi_out` at the bottom is the
finished statement.

The axiomatic proof in `Main.lean` explores the same diagram with `zx_explore`
and a dozen graph rewrites. Here it is a `calc` chain alternating two kinds of
step:

- **rebracketing**, discharged by `zx_iso` — the two terms describe the same
  diagram, so nothing has to be derived. This is what the axiomatic side never
  has to think about and what cost `cnot_cnot_rewrite` most of its twelve
  lines;
- **a rule**, by `zx_rw` — the only steps that actually change the diagram.

Writing the rebracketed form out by hand is the price: `zx_iso` proves a
rebracketing but does not choose one.

Nine rules and seven rebracketings in all. Only one `sorry` is reached — the
whole chain rests on `colour_change_X_one`, through `xPi_past_hadamard`; every
other local fact below is proved outright.
-/

-- Draw each goal as LHS/RHS diagrams in the InfoView as the cursor moves, which
-- is worth having here: this file is one long derivation and each step is a
-- picture.
show_panel_widgets [local SpLean.ZXPanel, local ProofWidgets.SelectionPanel]

def ex37a : ZX 2 3 := (.wire ⊗ .wire ⊗ .spider .Z 0 1) ≫ (.wire ⊗ Gate.NOTC)
def ex37b : ZX 3 3 := .wire ⊗ .hadamard ⊗ .spider .X 1 1 π
def ex37c : ZX 3 2 := Gate.NOTC ⊗ .spider .X 1 0
def ex37d : ZX 2 2 := (.wire ⊗ .hadamard) ≫ Gate.CX
def ex37 : ZX 2 2 := ((ex37a ≫ ex37b) ≫ ex37c) ≫ ex37d

/-! ### Two local facts

Both are spider fusion where the spider being absorbed meets only *one* leg of
its partner, with the other legs passing by. The general form of that is
`zSpider_fusion_spectator`, still a `sorry`; at these concrete arities the
semantics settles them directly. -/

/-- A Z state fuses into one input of a Z spider, leaving an identity spider. -/
theorem zState_fusion :
    ((ZX.wire ⊗ ZX.spider .Z 0 1) ≫ ZX.spider .Z 2 1) ≈zx ZX.spider .Z 1 1 := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, zSpiderSem, AlgPhase.expI_zero]
  rw [sum_wires2]
  cases hf : f 0 <;> cases hg : g 0 <;> simp [hf, hg]

/-- An X effect fuses into one output of an X spider, taking its phase with it. -/
theorem xEffect_fusion :
    (ZX.spider .X 1 2 ≫ (ZX.wire ⊗ ZX.spider .X 1 0 π)) ≈zx ZX.spider .X 1 1 π := by
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hsq4 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 4 = 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
    norm_num
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, xSpiderSem, zSpiderSem, hadSem, sum_wires1, sum_wires2]
  cases hf : f 0 <;> cases hg : g 0 <;>
    simp [hf, hg, sum_wires1, zeroAmpl, oneAmpl] <;> ring_nf <;> norm_num [hsq, hsq4]

/-- The whole first layer collapses: the `Z` state fuses into the `NOTC`'s `Z`
spider, which is then a phase-free two-legged spider — a wire. -/
theorem ex37a_simp : ex37a ≈zx (ZX.wire ⊗ ZX.spider .X 1 2) := by
  calc ex37a
      ≈zx ZX.wire ⊗ (ZX.spider .X 1 2
            ≫ (ZX.wire ⊗ ((ZX.wire ⊗ ZX.spider .Z 0 1) ≫ ZX.spider .Z 2 1))) := by zx_iso
    _ ≈zx ZX.wire ⊗ (ZX.spider .X 1 2 ≫ (ZX.wire ⊗ ZX.spider .Z 1 1)) := by
        zx_rw [zState_fusion]
    _ ≈zx ZX.wire ⊗ (ZX.spider .X 1 2 ≫ (ZX.wire ⊗ ZX.wire)) := by
        zx_rw [identity_removal_Z]
    _ ≈zx ZX.wire ⊗ ZX.spider .X 1 2 := by zx_iso

/-- **The rearrangement.** The π starts buried in the middle of the diagram, on
the third qubit of `ex37b`, and ends up as a single `X(π)` on the input wire —
with the entire first layer (a `Z` state and a `NOTC`, three spiders) gone.

Every step is one of two kinds. The `zx_iso` steps are *rebracketings*: the
term is rewritten into one describing the same diagram, which is where all the
work went in `cnot_cnot_rewrite` and is now free. The `zx_rw` steps are the
three that actually change the diagram — one fusion each.

The rebracketings are doing more than re-associating. The second one re-cuts
`ex37b` and `ex37c` (which split their rows `1|1|1` and `2|1`) so that the π
spider and the X effect become adjacent, and the fourth pulls a Hadamard out
from between a spider and its effect. Both are things `stack_interchange`
cannot do, because the wires cross the cut.

No `sorry`: the two local fusions above are proved, and `zx_iso` rests on
`Iso.sem_eq` and `sem_toHyp`. -/
theorem ex37_pi_to_input :
    ex37 ≈zx ((ZX.wire ⊗ (ZX.spider .X 1 1 π ≫ ZX.hadamard)) ≫ Gate.NOTC) ≫ ex37d := by
  calc ex37
      ≈zx (((ZX.wire ⊗ ZX.spider .X 1 2) ≫ ex37b) ≫ ex37c) ≫ ex37d := by
        unfold ex37
        zx_rw [ex37a_simp]
    -- Re-cut so the π spider meets the X effect.
    _ ≈zx ((ZX.wire ⊗ (ZX.spider .X 1 2
            ≫ (ZX.hadamard ⊗ (ZX.spider .X 1 1 π ≫ ZX.spider .X 1 0)))) ≫ Gate.NOTC) ≫ ex37d := by
        unfold ex37b ex37c
        zx_iso
    _ ≈zx ((ZX.wire ⊗ (ZX.spider .X 1 2 ≫ (ZX.hadamard ⊗ ZX.spider .X 1 0 π)))
            ≫ Gate.NOTC) ≫ ex37d := by zx_rw [xSpider_fusion]
    -- Pull the Hadamard out from between the spider and its effect.
    _ ≈zx ((ZX.wire ⊗ ((ZX.spider .X 1 2 ≫ (ZX.wire ⊗ ZX.spider .X 1 0 π)) ≫ ZX.hadamard))
            ≫ Gate.NOTC) ≫ ex37d := by zx_iso
    _ ≈zx ((ZX.wire ⊗ (ZX.spider .X 1 1 π ≫ ZX.hadamard)) ≫ Gate.NOTC) ≫ ex37d := by
        zx_rw [xEffect_fusion]

/-! ### Moving a π around

Six local facts. All are concrete instances of rules that are still `sorry` in
the general case — spectator fusion, colour change, π-commutation — and at
these arities the semantics settles five of them outright. Only
`xPi_past_hadamard` leans on a stub (`colour_change_X_one`), and everything
downstream of it inherits that. -/

/-- Commute an X(π) past a Hadamard, turning it green. -/
theorem xPi_past_hadamard :
    (ZX.spider .X 1 1 π ≫ ZX.hadamard) ≈zx (ZX.hadamard ≫ ZX.spider .Z 1 1 π) := by
  calc (ZX.spider .X 1 1 π ≫ ZX.hadamard)
      ≈zx ((ZX.hadamard ≫ ZX.hadamard) ≫ ZX.spider .X 1 1 π) ≫ ZX.hadamard := by
        zx_rw [hadamard_hadamard, wire_compose]
    _ ≈zx ZX.hadamard ≫ ((ZX.hadamard ≫ ZX.spider .X 1 1 π) ≫ ZX.hadamard) := by zx_iso
    _ ≈zx ZX.hadamard ≫ ZX.spider .Z 1 1 π := by zx_rw [colour_change_X_one]

/-- A one-legged Z spider fuses into one input of a Z spider. -/
theorem zPi_fuse :
    ((ZX.wire ⊗ ZX.spider .Z 1 1 π) ≫ ZX.spider .Z 2 1) ≈zx ZX.spider .Z 2 1 π := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, zSpiderSem, AlgPhase.expI_zero]
  rw [sum_wires2]
  cases hf0 : f 0 <;> cases hf1 : f 1 <;> cases hg : g 0 <;> simp [hf0, hf1, hg]

/-- Onto the second `NOTC`: commute the π past the Hadamard and fuse it into
the `Z` spider there. -/
theorem ex37_pi_onto_notc :
    (((ZX.wire ⊗ (ZX.spider .X 1 1 π ≫ ZX.hadamard)) ≫ Gate.NOTC) ≫ ex37d)
      ≈zx (((ZX.wire ⊗ ZX.hadamard) ≫ (ZX.spider .X 1 2 ⊗ ZX.wire))
            ≫ (ZX.wire ⊗ ZX.spider .Z 2 1 π : ZX 3 2)) ≫ ex37d := by
  calc (((ZX.wire ⊗ (ZX.spider .X 1 1 π ≫ ZX.hadamard)) ≫ Gate.NOTC) ≫ ex37d)
      ≈zx ((ZX.wire ⊗ (ZX.hadamard ≫ ZX.spider .Z 1 1 π)) ≫ Gate.NOTC) ≫ ex37d := by
        zx_rw [xPi_past_hadamard]
    _ ≈zx (((ZX.wire ⊗ ZX.hadamard) ≫ (ZX.spider .X 1 2 ⊗ ZX.wire))
            ≫ (ZX.wire ⊗ ((ZX.wire ⊗ ZX.spider .Z 1 1 π) ≫ ZX.spider .Z 2 1) : ZX 3 2)) ≫ ex37d := by
        zx_iso
    _ ≈zx (((ZX.wire ⊗ ZX.hadamard) ≫ (ZX.spider .X 1 2 ⊗ ZX.wire))
            ≫ (ZX.wire ⊗ ZX.spider .Z 2 1 π : ZX 3 2)) ≫ ex37d := by
        zx_rw [zPi_fuse]

theorem zUnfuse_pi : ZX.spider .Z 2 1 π ≈zx (ZX.spider .Z 2 1 ≫ ZX.spider .Z 1 1 π) := by
  simpa using (zSpider_fusion 2 1 0 π).symm

theorem zPi_past_hadamard :
    (ZX.spider .Z 1 1 π ≫ ZX.hadamard) ≈zx (ZX.hadamard ≫ ZX.spider .X 1 1 π) := by
  calc (ZX.spider .Z 1 1 π ≫ ZX.hadamard)
      ≈zx ((ZX.hadamard ≫ ZX.hadamard) ≫ ZX.spider .Z 1 1 π) ≫ ZX.hadamard := by
        zx_rw [hadamard_hadamard, wire_compose]
    _ ≈zx ZX.hadamard ≫ ((ZX.hadamard ≫ ZX.spider .Z 1 1 π) ≫ ZX.hadamard) := by zx_iso
    _ ≈zx ZX.hadamard ≫ ZX.spider .X 1 1 π := by zx_rw [colour_change_one]

theorem pi_copy_Z21 :
    ((ZX.wire ⊗ ZX.spider .X 1 1 π) ≫ ZX.spider .Z 2 1)
      ≈zx ((ZX.spider .X 1 1 π ⊗ ZX.wire) ≫ ZX.spider .Z 2 1) ≫ ZX.spider .X 1 1 π := by
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, xSpiderSem, zSpiderSem, hadSem, sum_wires1, sum_wires2,
    AlgPhase.expI_one, AlgPhase.expI_zero]
  cases hf0 : f 0 <;> cases hf1 : f 1 <;> cases hg : g 0 <;>
    simp [hf0, hf1, hg, sum_wires1, sum_wires2, zeroAmpl, oneAmpl] <;> ring_nf <;>
      norm_num [hsq]

/-- A π on one output leg of a Z spider can be moved to the other. -/
theorem zPi_swap_legs :
    (ZX.spider .Z 1 2 ≫ (ZX.wire ⊗ ZX.spider .Z 1 1 π))
      ≈zx (ZX.spider .Z 1 2 ≫ (ZX.spider .Z 1 1 π ⊗ ZX.wire)) := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, zSpiderSem, AlgPhase.expI_one, AlgPhase.expI_zero]
  rw [sum_wires2, sum_wires2]
  cases hf : f 0 <;> cases hg0 : g 0 <;> cases hg1 : g 1 <;> simp [hf, hg0, hg1]

/-- Through the `CX`: unfuse the π, commute it past the next Hadamard, and
π-copy it through the final `Z` spider — which puts one copy on an output. -/
theorem ex37_pi_through_cx :
    ((((ZX.wire ⊗ ZX.hadamard) ≫ (ZX.spider .X 1 2 ⊗ ZX.wire))
        ≫ (ZX.wire ⊗ ZX.spider .Z 2 1 π : ZX 3 2)) ≫ ex37d)
      ≈zx (((ZX.wire ⊗ ZX.hadamard) ≫ (ZX.spider .X 1 2 ⊗ ZX.wire))
            ≫ (ZX.wire ⊗ ZX.spider .Z 2 1 : ZX 3 2))
          ≫ ((ZX.wire ⊗ ZX.hadamard)
            ≫ (((ZX.spider .Z 1 2 ⊗ ZX.wire) ≫ (ZX.wire ⊗ ZX.hadamard ⊗ ZX.wire))
              ≫ (ZX.wire ⊗ (((ZX.spider .X 1 1 π ⊗ ZX.wire) ≫ ZX.spider .Z 2 1)
                   ≫ ZX.spider .X 1 1 π) : ZX 3 2))) := by
  calc ((((ZX.wire ⊗ ZX.hadamard) ≫ (ZX.spider .X 1 2 ⊗ ZX.wire))
          ≫ (ZX.wire ⊗ ZX.spider .Z 2 1 π : ZX 3 2)) ≫ ex37d)
      -- Unfuse the π off the spider.
      ≈zx (((ZX.wire ⊗ ZX.hadamard) ≫ (ZX.spider .X 1 2 ⊗ ZX.wire))
            ≫ (ZX.wire ⊗ (ZX.spider .Z 2 1 ≫ ZX.spider .Z 1 1 π) : ZX 3 2)) ≫ ex37d := by
        zx_rw [zUnfuse_pi]
      -- Slide it up against the next Hadamard, then commute it past.
    _ ≈zx (((ZX.wire ⊗ ZX.hadamard) ≫ (ZX.spider .X 1 2 ⊗ ZX.wire))
            ≫ (ZX.wire ⊗ ZX.spider .Z 2 1 : ZX 3 2))
          ≫ ((ZX.wire ⊗ (ZX.spider .Z 1 1 π ≫ ZX.hadamard)) ≫ Gate.CX) := by
        unfold ex37d
        zx_iso
    _ ≈zx (((ZX.wire ⊗ ZX.hadamard) ≫ (ZX.spider .X 1 2 ⊗ ZX.wire))
            ≫ (ZX.wire ⊗ ZX.spider .Z 2 1 : ZX 3 2))
          ≫ ((ZX.wire ⊗ (ZX.hadamard ≫ ZX.spider .X 1 1 π)) ≫ Gate.CX) := by
        zx_rw [zPi_past_hadamard]
      -- Carry it down to the CX's Z spider, then π-copy through it.
    _ ≈zx (((ZX.wire ⊗ ZX.hadamard) ≫ (ZX.spider .X 1 2 ⊗ ZX.wire))
            ≫ (ZX.wire ⊗ ZX.spider .Z 2 1 : ZX 3 2))
          ≫ ((ZX.wire ⊗ ZX.hadamard)
            ≫ (((ZX.spider .Z 1 2 ⊗ ZX.wire) ≫ (ZX.wire ⊗ ZX.hadamard ⊗ ZX.wire))
              ≫ (ZX.wire ⊗ ((ZX.wire ⊗ ZX.spider .X 1 1 π) ≫ ZX.spider .Z 2 1)
                   : ZX 3 2))) := by
        unfold Gate.CX
        zx_iso
    _ ≈zx _ := by zx_rw [pi_copy_Z21]

/-- The other copy: carry it back past the Hadamard, onto the `Z` spider it
came from, and out along the other output. -/
theorem ex37_pi_to_outputs :
    ((((ZX.wire ⊗ ZX.hadamard) ≫ (ZX.spider .X 1 2 ⊗ ZX.wire))
        ≫ (ZX.wire ⊗ ZX.spider .Z 2 1 : ZX 3 2))
      ≫ ((ZX.wire ⊗ ZX.hadamard)
        ≫ (((ZX.spider .Z 1 2 ⊗ ZX.wire) ≫ (ZX.wire ⊗ ZX.hadamard ⊗ ZX.wire))
          ≫ (ZX.wire ⊗ (((ZX.spider .X 1 1 π ⊗ ZX.wire) ≫ ZX.spider .Z 2 1)
               ≫ ZX.spider .X 1 1 π) : ZX 3 2))))
      ≈zx (((ZX.wire ⊗ ZX.hadamard) ≫ Gate.NOTC) ≫ ex37d)
            ≫ (ZX.spider .Z 1 1 π ⊗ ZX.spider .X 1 1 π) := by
  calc ((((ZX.wire ⊗ ZX.hadamard) ≫ (ZX.spider .X 1 2 ⊗ ZX.wire))
          ≫ (ZX.wire ⊗ ZX.spider .Z 2 1 : ZX 3 2))
        ≫ ((ZX.wire ⊗ ZX.hadamard)
          ≫ (((ZX.spider .Z 1 2 ⊗ ZX.wire) ≫ (ZX.wire ⊗ ZX.hadamard ⊗ ZX.wire))
            ≫ (ZX.wire ⊗ (((ZX.spider .X 1 1 π ⊗ ZX.wire) ≫ ZX.spider .Z 2 1)
                 ≫ ZX.spider .X 1 1 π) : ZX 3 2))))
      -- G: group the copied π with the Hadamard in front of it, and commute.
      ≈zx (((ZX.wire ⊗ ZX.hadamard) ≫ (ZX.spider .X 1 2 ⊗ ZX.wire))
            ≫ (ZX.wire ⊗ ZX.spider .Z 2 1 : ZX 3 2))
          ≫ ((ZX.wire ⊗ ZX.hadamard)
            ≫ (((ZX.spider .Z 1 2 ⊗ ZX.wire)
                 ≫ ((ZX.wire ⊗ (ZX.hadamard ≫ ZX.spider .X 1 1 π)) ⊗ ZX.wire))
              ≫ (ZX.wire ⊗ (ZX.spider .Z 2 1 ≫ ZX.spider .X 1 1 π) : ZX 3 2))) := by
        zx_iso
    _ ≈zx (((ZX.wire ⊗ ZX.hadamard) ≫ (ZX.spider .X 1 2 ⊗ ZX.wire))
            ≫ (ZX.wire ⊗ ZX.spider .Z 2 1 : ZX 3 2))
          ≫ ((ZX.wire ⊗ ZX.hadamard)
            ≫ (((ZX.spider .Z 1 2 ⊗ ZX.wire)
                 ≫ ((ZX.wire ⊗ (ZX.spider .Z 1 1 π ≫ ZX.hadamard)) ⊗ ZX.wire))
              ≫ (ZX.wire ⊗ (ZX.spider .Z 2 1 ≫ ZX.spider .X 1 1 π) : ZX 3 2))) := by
        zx_rw [← zPi_past_hadamard]
      -- H: put the π next to the spider it came from, then move it to the other leg.
    _ ≈zx (((ZX.wire ⊗ ZX.hadamard) ≫ (ZX.spider .X 1 2 ⊗ ZX.wire))
            ≫ (ZX.wire ⊗ ZX.spider .Z 2 1 : ZX 3 2))
          ≫ ((ZX.wire ⊗ ZX.hadamard)
            ≫ ((((ZX.spider .Z 1 2 ≫ (ZX.wire ⊗ ZX.spider .Z 1 1 π)) ⊗ ZX.wire)
                 ≫ ((ZX.wire ⊗ ZX.hadamard) ⊗ ZX.wire))
              ≫ (ZX.wire ⊗ (ZX.spider .Z 2 1 ≫ ZX.spider .X 1 1 π) : ZX 3 2))) := by
        zx_iso
    _ ≈zx (((ZX.wire ⊗ ZX.hadamard) ≫ (ZX.spider .X 1 2 ⊗ ZX.wire))
            ≫ (ZX.wire ⊗ ZX.spider .Z 2 1 : ZX 3 2))
          ≫ ((ZX.wire ⊗ ZX.hadamard)
            ≫ ((((ZX.spider .Z 1 2 ≫ (ZX.spider .Z 1 1 π ⊗ ZX.wire)) ⊗ ZX.wire)
                 ≫ ((ZX.wire ⊗ ZX.hadamard) ⊗ ZX.wire))
              ≫ (ZX.wire ⊗ (ZX.spider .Z 2 1 ≫ ZX.spider .X 1 1 π) : ZX 3 2))) := by
        zx_rw [zPi_swap_legs]
      -- I: both π's are now on output wires; float them to the end.
    _ ≈zx (((ZX.wire ⊗ ZX.hadamard) ≫ Gate.NOTC) ≫ ex37d)
          ≫ (ZX.spider .Z 1 1 π ⊗ ZX.spider .X 1 1 π) := by
        unfold ex37d Gate.NOTC Gate.CX
        zx_iso

/-- **The rearrangement, finished.** `ex37` is a phase-free diagram followed by
a π on each output wire.

Nine rule applications and seven rebracketings. Every rebracketing is a
`zx_iso` — the terms describe the same diagram, so there is nothing to derive —
and they are what makes each rule's redex visible in the first place. That
division is the point: the ZX content is the nine `zx_rw`s, and the bookkeeping
that used to dominate a derivation is now a tactic call. -/
theorem ex37_pi_out :
    ex37 ≈zx (((ZX.wire ⊗ ZX.hadamard) ≫ Gate.NOTC) ≫ ex37d)
            ≫ (ZX.spider .Z 1 1 π ⊗ ZX.spider .X 1 1 π) :=
  ((ex37_pi_to_input.trans ex37_pi_onto_notc).trans ex37_pi_through_cx).trans
    ex37_pi_to_outputs

