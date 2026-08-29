import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Complex.Basic

/-!
# Hypergraphs

A ZX diagram as a combinatorial object that has forgotten how the term it came
from was bracketed. The encoding is the **incidence dual** of the picture the
renderer draws:

- a **vertex** is a *wire*, including the ones the term never names — the wire
  between the two spiders in `Z ≫ Z` is a vertex;
- a **hyperedge** (`boxes` below) is a *generator* — a spider or a Hadamard —
  carrying its label and the list of wires on its legs;
- the **boundary** says which wire each input and output port is.

That way round because it makes composition a *vertex merge*: `a ≫ b` is the
disjoint union with `a`'s output wire `i` identified with `b`'s input wire `i`.
The other way round (generators as vertices, wires as edges) would have to
merge edges and renumber. Vertex merging is also the presentation DPO rewriting
is stated in, should that ever follow.

## Identifications rather than a quotient

`compose` does not renumber. It keeps both wires and records the pair in
`ids`, and `Hypergraph.sem` carries a `[a v = a v']` factor for each recorded
pair. The delta is what stops a merged-away wire from being summed over freely
and multiplying the denotation by two.

The cost is that a `Hyp` is not a normal form: two `Hyp`s can describe the same
diagram with different `ids`. Isomorphism therefore has to work up to the
identifications (or normalise first) — see `PLAN.md`.

## Not enforced here

Anything `SpLean.Algebraic.toHyp` produces satisfies two invariants that the
definitions below do not demand, and that the merge relies on:

- every wire has degree exactly 2, counting boundary ports as ends;
- the input wires are pairwise distinct, and so are the outputs — a wire has
  two ends and no term can make both of them inputs. So the merge pairs up two
  disjoint `m`-element sets.

A `hadamard` box always has exactly two legs. `Hypergraph.sem` gives a junk
value rather than an error if it does not, which is the usual trade for keeping
the definition total.
-/

namespace SpLean.Hypergraph

/-- A boundary assignment: one bit per port. Definitionally `SpLean.Algebraic`'s
`Wires`, so the lowering theorem can be stated between them. -/
abbrev Bits (n : ℕ) := Fin n → Bool

/-- Spider colour. A third copy, after `SpiderColor` in `Axiomatic/` and
`AlgSpColor` in `Algebraic/`; see the root `CLAUDE.md` on why these are
duplicated rather than shared. -/
inductive Colour where
  | Z
  | X
  deriving Repr, BEq, DecidableEq

/-- What sits on a hyperedge. Parameterised by the phase type: a hypergraph
does not care what a phase is, only that `sem` is handed a way to turn one into
a complex number, so neither representation's phase type has to be imported
here. -/
inductive Label (Φ : Type) where
  | spider (c : Colour) (φ : Φ)
  | hadamard
  deriving Repr, DecidableEq

/-- One generator: a label, how many legs it has, and which wire each leg is on.

The leg count is a field rather than the length of a list of legs, so that the
leg tensor's arity is a plain `ℕ`. With legs as a list its arity would be a
`List.length` and every lemma about a box's tensor would have to transport
along `List.length_ofFn` — a dependent rewrite in a type index. The phase 0
spike changed this, and phase 1 made the same change to `boxes` and `ids`
below for the same reason: nothing here is a `List`. -/
structure Box (Φ : Type) (w : ℕ) where
  /-- What kind of generator this is. -/
  label : Label Φ
  /-- How many legs it has. -/
  arity : ℕ
  /-- Which wire each leg is on. -/
  legs : Fin arity → Fin w

/-- A ZX diagram as a hypergraph, indexed by its arity so that the lowering
theorem states without a cast. -/
structure Hyp (Φ : Type) (n m : ℕ) where
  /-- Number of wires; vertex ids are `Fin wires`. -/
  wires : ℕ
  /-- Number of generators. -/
  boxCount : ℕ
  /-- The generators. -/
  boxes : Fin boxCount → Box Φ wires
  /-- Number of wire pairs composition has identified. -/
  idCount : ℕ
  /-- The identified pairs. -/
  ids : Fin idCount → Fin wires × Fin wires
  /-- Which wire each input port is. -/
  inputs : Fin n → Fin wires
  /-- Which wire each output port is. -/
  outputs : Fin m → Fin wires

/-- An assignment that respects the recorded identifications: the ones
`Hyp.sem` sums over, and the ones an isomorphism has to match up. -/
def Hyp.Sat {Φ : Type} {n m : ℕ} (H : Hyp Φ n m) (a : Fin H.wires → Bool) : Prop :=
  ∀ k, a (H.ids k).1 = a (H.ids k).2

instance {Φ : Type} {n m : ℕ} (H : Hyp Φ n m) : DecidablePred H.Sat :=
  fun _ => inferInstanceAs (Decidable (∀ _, _))

end SpLean.Hypergraph
