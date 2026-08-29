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

/-- The π phase meets the X effect and is absorbed by it.

The π sits on the third qubit of `ex37b` and the X effect on the third qubit of
`ex37c`, so they are composed — but the term does not say so anywhere. `ex37b`
cuts its three rows `1 | 1 | 1` and `ex37c` cuts them `2 | 1`, so the two
spiders are buried on opposite sides of a `≫` that brackets them apart. The
first step re-cuts both layers `2 | 1`, which puts `X 1 1 π ≫ X 1 0` together
as a subterm; the second fuses them.

Both steps rest on proved facts — `Iso.sem_eq`/`sem_toHyp` for the first and
`xSpider_fusion` for the second — so this carries no `sorry`. -/
theorem ex37_absorb_pi : ex37 ≈zx
    (ex37a ≫ (((ZX.wire ⊗ ZX.hadamard) ≫ Gate.NOTC) ⊗ ZX.spider .X 1 0 π)) ≫ ex37d := by
  calc ex37
      ≈zx (ex37a ≫ (((ZX.wire ⊗ ZX.hadamard) ≫ Gate.NOTC)
            ⊗ (ZX.spider .X 1 1 π ≫ ZX.spider .X 1 0))) ≫ ex37d := by
        unfold ex37 ex37a ex37b ex37c ex37d
        zx_iso
    _ ≈zx (ex37a ≫ (((ZX.wire ⊗ ZX.hadamard) ≫ Gate.NOTC)
            ⊗ ZX.spider .X 1 0 π)) ≫ ex37d := by
        zx_rw [xSpider_fusion]

/-! ### Where it stops, and why

The next move would be the `Z 0 1` state inside `ex37a` fusing into the `Z 2 1`
of that `Gate.NOTC`. `zx_iso` can rebracket the term to put them adjacent, but
the state feeds *one* of that spider's two inputs, with the other passing by —
which is `zSpider_fusion_spectator`, still a `sorry` in
`SpLean/Algebraic/Rules/SpiderFusion.lean`.

So the chain is limited by which rules are proved, not by the machinery: every
structural step along the way is now free. -/

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
