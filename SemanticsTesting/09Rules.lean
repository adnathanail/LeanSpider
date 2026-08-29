import SemanticsTesting.Utils
import SemanticsTesting.«07Stack»
import ProofWidgets.Component.Panel.SelectionPanel

open SpLean.Algebraic

-- Draw each goal as LHS/RHS diagrams in the InfoView as the cursor moves.
show_panel_widgets [local SpLean.ZXPanel, local ProofWidgets.SelectionPanel]

-- two_t_gates_equiv_s_gate
example :
    Gate.T ≫ Gate.T ≈zx Gate.S := by
  zx_rw [spider_fusion_Z_one_wire]

-- three_t_gates_fusion
example :
    Gate.T ≫ Gate.T ≫ Gate.T ≈zx ZX.spider .Z 1 1 (3π/4) := by
  zx_rw [spider_fusion_Z_one_wire, spider_fusion_Z_one_wire]

-- two_x_gates_fusion
example :
    Gate.X ≫ Gate.X ≈zx ZX.spider .X 1 1 (2π) := by
  zx_rw [spider_fusion_X_one_wire]

-- fuse_under_stack
example :
    (ZX.wire ⊗ (ZX.hadamard ≫ (Gate.T ≫ Gate.T))) ≈zx
      (ZX.wire ⊗ (ZX.hadamard ≫ Gate.S)) := by
  zx_rw [spider_fusion_Z_one_wire]

-- fuse_symbolic
example (α β γ : AlgPhase) :
    ((ZX.spider .Z 1 1 α ≫ ZX.spider .Z 1 1 β) ≫ ZX.spider .Z 1 1 γ) ≈zx
      ZX.spider .Z 1 1 (α + β + γ) := by
  zx_rw [spider_fusion_Z_one_wire, spider_fusion_Z_one_wire]

-- unfuse
example (α β : AlgPhase) :
    ZX.spider .Z 1 1 (α + β) ≈zx (ZX.spider .Z 1 1 α ≫ ZX.spider .Z 1 1 β) := by
  zx_rw [← spider_fusion_Z_one_wire]

-- colour_change_fusion
example :
    Gate.Z ≫ ZX.hadamard ≫ Gate.X  ≫ ZX.hadamard ≈zx Gate.I := by
  unfold Gate.Z Gate.X Gate.I
  -- Colour change
  zx_rw [colour_change_X_Z_one_wire]
  repeat grw [compose_assoc]
  -- Expose the inner Hadamard pair, then cancel both pairs at once
  grw [← compose_assoc ZX.hadamard ZX.hadamard]
  zx_rw [hadamard_hadamard, wire_compose, compose_wire]
  -- Spider fusion
  zx_rw [spider_fusion_Z_one_wire]
  zx_phase
  zx_rw [identity_removal_Z_two_pi, identity_removal_Z_zero]

-- two_pi_spider_is_phaseless
example :
    ZX.spider .Z 0 1 (2π) ≈zx ZX.spider .Z 0 1 0 := by
  zx_rw [spider_normalize]
  zx_normalize

-- three_pi_spider_is_pi
example :
    ZX.spider .X 1 1 (3π) ≈zx ZX.spider .X 1 1 π := by
  zx_rw [spider_normalize]
  zx_normalize

/-- The rule fires inside a larger diagram, not only at the top. -/
-- two_pi_spider_normalizes_under_compose
example :
    (ZX.spider .Z 0 1 (2π) ≫ ZX.hadamard) ≈zx (ZX.spider .Z 0 1 0 ≫ ZX.hadamard) := by
  zx_rw [spider_normalize]
  zx_normalize

-- pqs p123
-- euler_decomp1
example :
    Gate.S ≫ ZX.hadamard ≫ Gate.S ≈zx ZX.spider .X 1 1 (-π/2) := by
  zx_rw [euler_decomp_ZXZ]
  repeat grw [compose_assoc]
  -- Fuse the trailing pair, then regroup to expose the leading one
  zx_rw [spider_fusion_Z_one_wire]
  grw [← compose_assoc]
  zx_rw [spider_fusion_Z_one_wire]
  zx_normalize
  zx_rw [← compose_assoc]
  zx_rw [pi_copy_X]
  zx_rw [nStack_one]
  zx_rw [compose_assoc]
  zx_rw [spider_fusion_Z]
  zx_normalize
  zx_rw [identity_removal_Z_two_pi]
  zx_rw [compose_wire]

-- big_fusion
example :
    ZX.spider .Z 1 5 (π) ≫ ZX.spider .Z 5 1 (π/2) ≫ (ZX.spider .X 1 3 ≫ ZX.spider .X 3 4  ≫ ZX.spider .X 4 1) ≈zx
      ZX.spider .Z 1 1 (3π/2) ≫ ZX.spider .X 1 1 := by
  grw [← compose_assoc]
  zx_rw [spider_fusion_Z]
  grw [← compose_assoc]
  zx_rw [spider_fusion_X]
  grw [compose_assoc]
  zx_rw [spider_fusion_X]

-- had_pushing
example (α β : AlgPhase) :
    ZX.hadamard ≫ ZX.spider .Z 1 1 α ≫ ZX.spider .X 1 1 π ≫ ZX.spider .Z 1 1 β ≫ ZX.spider .X 1 1 (3π/2) ≈zx
      ZX.spider .X 1 1 α ≫ ZX.spider .Z 1 1 π ≫ ZX.spider .X 1 1 β ≫ ZX.spider .Z 1 1 (3π/2) ≫ ZX.hadamard := by
  -- Push the Hadamard rightwards one spider at a time: colour-change the spider
  -- it faces, which emits a Hadamard that cancels against it. Each rule is given
  -- its phase explicitly, so it fires at that spider and nowhere else.
  zx_rw [colour_change_Z_X_one_wire α]
  repeat grw [compose_assoc]
  grw [← compose_assoc ZX.hadamard ZX.hadamard]
  zx_rw [hadamard_hadamard, wire_compose]
  zx_rw [colour_change_X_Z_one_wire π]
  repeat grw [compose_assoc]
  grw [← compose_assoc ZX.hadamard ZX.hadamard]
  zx_rw [hadamard_hadamard, wire_compose]
  zx_rw [colour_change_Z_X_one_wire β]
  repeat grw [compose_assoc]
  grw [← compose_assoc ZX.hadamard ZX.hadamard]
  zx_rw [hadamard_hadamard, wire_compose]
  zx_rw [colour_change_X_Z_one_wire (3π/2)]
  grw [← compose_assoc ZX.hadamard ZX.hadamard]
  zx_rw [hadamard_hadamard, wire_compose]

def pushMe := ZX.spider .X 0 1 ≫ ZX.spider .Z 1 5
#zx pushMe
def imPushed := ZX.spider .X 0 1 ⊗ ZX.spider .X 0 1 ⊗ ZX.spider .X 0 1 ⊗ ZX.spider .X 0 1 ⊗ ZX.spider .X 0 1
#zx imPushed
example :
    pushMe ≈zx imPushed := by
  unfold pushMe imPushed
  zx_rw [state_copy_Z_zero]
  simp only [ZX.nStackState]
  -- Reassociate
  repeat zx_rw [← stack_assoc]
  -- Drop the `ZX.empty` that `nStackState 0` left at the bottom of the stack.
  zx_rw [empty_stack']

/-! ## Exercise 3.7, algebraically

The diagram `exercise3point7` in `Main.lean`, as an algebraic term. The
axiomatic proof there explores it with `zx_explore` and a dozen graph rewrites;
here the aim is the same rearrangement, but written as a `calc` chain that
alternates two kinds of step:

- **rebracketing**, discharged by `zx_iso` — the two terms describe the same
  diagram, so nothing has to be derived. This is what the axiomatic side never
  has to think about and what cost `cnot_cnot_rewrite` most of its twelve
  lines;
- **a rule**, by `zx_rw` — the only steps that actually change the diagram.

Writing the rebracketed form out by hand is the price: `zx_iso` proves a
rebracketing but does not choose one. -/

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

/-! ### Where it stops

The π is now on the input wire. Pushing it through to the *output* would go:
colour change past the Hadamard (`colour_change_X_one`), fuse into the second
`NOTC`'s Z spider, then π-copy it through the `CX` (`pi_copy_Z`) — all three
still `sorry`. The structural steps between them would again be `zx_iso`. -/

/-- The two CNOT decompositions agree.

`stack_interchange` cannot fire here, and no argument order or `ZX.cast` will
change that. Interchange needs both layers to cut the middle boundary in the
same place — its conclusion mentions `a ≫ b`, so that composition has to
typecheck — and these cut `2 | 1` and `1 | 2`, because the wire joining the two
spiders crosses the cut. A cast repairs arities of different *shape*; these are
already both `ZX 2 2`.

What separates the two forms is which way that joining wire is composed, so
turning one into the other means *bending* it: the `bend_*` rules in
`SpLean/Algebraic/Rules/Yank.lean`. That derivation is carried out in
`cnot_cnot_rewrite` below. Computing is the short way, and `of_sem_eq`
lifts the already-proved `cnot_sem_agnostic` (`07Stack.lean`) to `≈zx`. -/
theorem cnot_cnot_equiv :
    Gate.CNOT ≈zx Gate.CNOT' :=
  ZX.Equiv.of_sem_eq cnot_sem_agnostic

/-- The same fact by rewriting rather than by computing.

The two forms are the same graph — a Z spider and an X spider joined by an
edge — composed in opposite directions, so the derivation is: bend the joining
leg on each side until both diagrams put the two spiders in *parallel*, joined
by a cap, and then the two sides are literally the same term.

Phase by phase:

1. **Bend.** The Z-first form's `X 2 1` has the joining leg as its first input;
   bending it round *above* makes it a first output. The X-first form's
   `Z 2 1` bends its last input round *below*. Both sides now hold a `Z 1 2`
   and an `X 1 2` with a cap.
2. **Split.** Each bend leaves a `≫` inside one row of a `⊗`, which no rule
   matches; `stack_compose_below`/`stack_compose_above` put those back into
   layers.
3. **Regroup.** The two layers still cut their shared boundary in different
   places, which is what stopped `stack_interchange` at the start. Now it can
   be fixed: `stack_assoc`/`stack_assoc_symm` move the bracket so both layers
   cut alike, and `compose_assoc` brings the two layers next to each other.
4. **Interchange.** With the cuts aligned the two rows are independent, so the
   spiders separate: each side becomes `(Z 1 2 ⊗ X 1 2) ≫ (caps)`.
5. **Tidy.** `nWire`/`wire` identities clear the padding, and one last
   `stack_assoc_symm` brings the two cap layers into the same bracketing.

This rests on two stubs — `bend_output` and `bend_output_above` — so it does
not make `cnot_cnot_equiv` any more proved than the computation above already
does. (`stack_interchange` and the `nWire` identities it also uses started out
stubbed and are now proved.)
What it shows is that the rule set composes into a derivation, and it is a
regression test for `zx_rw`: if a rule statement or the tactic changes shape,
this breaks. -/
theorem cnot_cnot_rewrite :
    Gate.CNOT ≈zx Gate.CNOT' := by
  unfold Gate.CNOT Gate.CNOT'
  -- 1. Bend the joining leg: above on the X, below on the Z.
  zx_rw [← bend_output_above .X 1 1 0, ← bend_output .Z 1 1 0]
  simp only [ZX.cast_self]
  -- 2. Each bend left a `≫` inside a row of a `⊗`; split those into layers.
  zx_rw [stack_compose_below, stack_compose_above]
  -- 3. Regroup so both layers cut their shared boundary in the same place.
  zx_rw [← stack_assoc ZX.wire ZX.wire (ZX.spider .X 1 2),
         stack_assoc_symm (ZX.spider .Z 1 2) ZX.wire ZX.wire]
  simp only [ZX.cast_self]
  zx_rw [← compose_assoc (ZX.spider .Z 1 2 ⊗ ZX.wire),
         ← compose_assoc (ZX.wire ⊗ ZX.spider .X 1 2)]
  -- 4. The cuts now align, so the spiders separate into parallel rows.
  zx_rw [stack_interchange (ZX.spider .Z 1 2) (ZX.wire ⊗ ZX.wire) ZX.wire (ZX.spider .X 1 2),
         stack_interchange ZX.wire (ZX.spider .Z 1 2) (ZX.spider .X 1 2) (ZX.wire ⊗ ZX.wire)]
  -- 5. Clear the padding, then match the two cap layers' bracketing.
  zx_rw [← nWire_two, compose_nWire, compose_nWire, wire_compose, wire_compose]
  zx_rw [stack_assoc_symm (ZX.nWire 1) ZX.cap (ZX.nWire 1)]

/-- What a `stack_interchange` call looks like when the rule does apply: both
layers cut the boundary in the same place (`1 | 1`), so the two rows are
independent and each rewrites on its own. The four arguments are the cells in
composition order, top row then bottom — `a b` are `a ≫ b`, `c d` are
`c ≫ d`. -/
example : ((Gate.T ⊗ ZX.hadamard) ≫ (Gate.T ⊗ ZX.hadamard)) ≈zx (Gate.S ⊗ ZX.wire) := by
  zx_rw [stack_interchange Gate.T Gate.T ZX.hadamard ZX.hadamard]
  zx_rw [zSpider_fusion, hadamard_hadamard]
