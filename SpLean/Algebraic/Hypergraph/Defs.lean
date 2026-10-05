import SpLean.Algebraic.ZX

/-!
# Hypergraphs

A ZX diagram as a combinatorial object, with no record of how the term it came
from was bracketed. Two terms that differ only in bracketing, unit laws or
wire bending lower to isomorphic hypergraphs.

The encoding is the **incidence dual** of the picture the renderer draws:

- a **vertex** is a *wire*, including wires the term never names: in `Z ≫ Z`
  the wire between the two spiders is a vertex;
- a **hyperedge** (a `Box`) is a *generator*, a spider or a Hadamard, carrying
  its label and the wire on each of its legs;
- the **boundary** says which wire each input and output port is.

This orientation makes composition a *vertex merge*: `a ≫ b` is the disjoint
union of `a` and `b` with `a`'s output wire `i` identified with `b`'s input
wire `i`. The opposite orientation (generators as vertices, wires as edges)
would make composition merge edges and renumber everything. Vertex merging is
also the setting in which double-pushout rewriting is stated.

## Identified wires

Composition does not renumber wires. It keeps both wires of each merged pair
and records the pair in `ids`. The semantics then includes a factor
`[a v = a v']` for every recorded pair `(v, v')`, forcing the two wires to
carry the same value; without it each wire would be summed over independently
and the denotation would come out doubled.

As a consequence a `Hyp` is not a normal form: two `Hyp`s can describe the same
diagram with different `ids`. Isomorphism has to be taken up to the
identifications, or the identifications normalised away first. `PLAN.md` has
the details.

## Invariants not captured by the types

Hypergraphs lowered from `ZX` terms satisfy two further invariants, which the
vertex merge relies on:

- every wire has degree exactly 2, counting boundary ports as ends;
- the input wires are pairwise distinct, as are the output wires. A wire has
  two ends and no term can make both of them inputs, so composition always
  pairs up two disjoint `m`-element sets of wires.

A `hadamard` box is expected to have exactly two legs. The semantics assigns a
junk value to one that does not, which keeps the definition total.
-/

namespace SpLean.Algebraic.Hypergraph

/-- The label on a hyperedge: a spider with its colour and phase, or a
Hadamard. -/
inductive Label where
  | spider (c : AlgSpColor) (φ : AlgPhase)
  | hadamard
  deriving Repr

/-- One generator: a label, how many legs it has, and which wire each leg is on.

The leg count is stored as a field, rather than derived as the length of a
`List` of legs, so that the arity of the box's tensor is a plain `ℕ`. Were it a
`List.length`, every lemma about a box's tensor would need to transport along
`List.length_ofFn`, a dependent rewrite inside a type index. `Hyp` stores its
boxes and identified pairs as counted functions for the same reason. -/
structure Box (w : ℕ) where
  /-- What kind of generator this is. -/
  label : Label
  /-- How many legs it has. -/
  arity : ℕ
  /-- Which wire each leg is on. -/
  legs : Fin arity → Fin w

/-- A ZX diagram with `n` inputs and `m` outputs, as a hypergraph. Indexed by
its arity so that it can be related to a `ZX n m` term without a cast. -/
structure Hyp (n m : ℕ) where
  /-- Number of wires; wire (vertex) ids are `Fin wires`. -/
  wires : ℕ
  /-- Number of generators. -/
  boxCount : ℕ
  /-- The generators. -/
  boxes : Fin boxCount → Box wires
  /-- Number of pairs of wires identified by composition. -/
  idCount : ℕ
  /-- The identified pairs: both wires in a pair carry the same value. -/
  ids : Fin idCount → Fin wires × Fin wires
  /-- Which wire each input port is. -/
  inputs : Fin n → Fin wires
  /-- Which wire each output port is. -/
  outputs : Fin m → Fin wires

end SpLean.Algebraic.Hypergraph
