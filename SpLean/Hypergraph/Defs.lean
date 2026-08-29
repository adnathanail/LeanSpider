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
  deriving Repr

/-- A ZX diagram as a hypergraph, indexed by its arity so that the lowering
theorem states without a cast. -/
structure Hyp (Φ : Type) (n m : ℕ) where
  /-- Number of wires; vertex ids are `Fin wires`. -/
  wires : ℕ
  /-- The generators: a label and the wires on its legs. -/
  boxes : List (Label Φ × List (Fin wires))
  /-- Wires that composition identified. -/
  ids : List (Fin wires × Fin wires)
  /-- Which wire each input port is. -/
  inputs : Fin n → Fin wires
  /-- Which wire each output port is. -/
  outputs : Fin m → Fin wires

end SpLean.Hypergraph
