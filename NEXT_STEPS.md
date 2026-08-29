# Next steps

Written at the end of the `hypergraphs` branch, when the hypergraph layer was
finished end to end (encoding → semantics → isomorphism invariance → lowering →
certificate → search → `zx_iso`). Module detail lives in
`SpLean/Hypergraph/CLAUDE.md` and `SpLean/Algebraic/CLAUDE.md`; this file is
only about what to do next.

## First: decide about `swap`

**`ZX` has no crossing, so it generates only *planar* diagrams.** That is not a
small corner — it is the single constraint behind most of what is still
missing, and it gets in the way of both options below. Reasons to settle it
before starting either:

- **Two standard rules cannot even be stated.** `SpLean/Algebraic/Rules/Bialgebra.lean`
  deliberately holds no theorem: bialgebra and strong complementarity both need
  a crossing, and a swap is *not* derivable from cups and caps — in a compact
  closed category the symmetry is what those are defined against.
- **Spider symmetry is only half-available.** The `bend_*` rules rotate a leg
  between the two ends of a spider; permuting two adjacent legs needs a swap.
  (The hypergraph layer has full symmetry, since a hyperedge has no leg order —
  which is exactly why `zx_iso` can prove things the rules cannot.)
- **A rewritten hypergraph may not come back.** Rewriting at the hypergraph
  level can produce a graph no term expresses, and there is no `Hyp → ZX`
  synthesis either. See option B.

**It is cheap now, and it was not before.** With the hypergraph layer in place
the lowering is trivial — a swap is two vertices, no hyperedges, and `outputs`
the reverse of `inputs` — and `Iso.sem_eq`, `sem_toHyp`'s other cases and the
whole certificate path need no change. The work is:

- a `swap : ZX 2 2` constructor, or a general `perm : Equiv.Perm (Fin n) → ZX n n`
  (strong complementarity wants the general one; `SpLean/Algebraic/CLAUDE.md`
  anticipates it under "permuting wires is reindexing a sum");
- a `ZX.sem` clause — for `swap`, `if f 0 = g 1 ∧ f 1 = g 0 then 1 else 0`;
- a `toHyp` clause (as above), and its case in `sem_toHyp`;
- layout in `Algebraic/Visualize.lean` and a case in `Algebraic/Render.lean`.

Do this first, or knowingly accept the planar restriction and say so where it
bites.

## Option A: automatic rebracketing (the near one)

A tactic — `zx_apply zSpider_fusion`, say — that searches the hypergraph for a
rule's redex, works out a bracketing that exposes it, proves *that* with the
existing certificate machinery, and then fires the rule.

This is the high-value tactic work, and it reuses everything already built:
`Search.lean` for the matching, `Iso.ofTables` for the certificate, `zx_rw` for
the firing. What it removes is exactly the manual half of
`SemanticsTesting/11Ex37.lean` — seven rebracketed terms typed out by hand so
that nine rules could fire. Those seven would become invisible.

The new work is choosing the target bracketing: given "these two spiders should
fuse", produce a term that puts them adjacent. That is a small synthesis
problem, and unlike option B it stays inside the terms the ADT can express.

## Option B: DPO rewriting (the research one)

What the encoding was chosen for. A rule becomes a pair of hypergraphs sharing
a boundary; match the left as a *subgraph*, cut it out, glue the right in.
Because the hypergraph has forgotten the bracketing, a rule matches whenever it
should rather than when the term happens to expose it. Wires-as-vertices makes
composition a pushout, which is the setting DPO is stated in — that is why that
encoding was picked over the dual one.

Needed: rules as spans of hypergraphs; subgraph matching (harder than the
whole-graph isomorphism `Search.lean` does today); pushout complement and
pushout; and a soundness theorem — rewriting inside preserves `≈zx`, given the
rule is sound.

**The obstacle is the planarity one above.** Either add `swap` so every
hypergraph has a term, or keep every *stated* equivalence between real terms
and use the hypergraph purely as the engine. Worth deciding explicitly rather
than discovering halfway.

## Smaller wins, any time

- **`colour_change_X_one`** (`Rules/ColourChange.lean`) is one `sorry` and
  would make the whole of `SemanticsTesting/11Ex37.lean` sorry-free —
  `xPi_past_hadamard` is derived from it and everything downstream inherits it.
- **The 29 remaining rule stubs.** `11Ex37.lean` proves concrete instances of
  three of the general ones (spectator fusion, colour change, π-commutation)
  and five of its six local facts fell to `sum_wires2` plus a case split, so
  those are decent templates — the general proofs may be more accessible than
  the stub count suggests.
- **`Axiomatic/ToHypergraph.lean`.** A second lowering, plus its own
  `sem_toHyp`, would finally give the axioms in `Axiomatic/Rules/` a soundness
  target. This is the *reason* `Algebraic/` exists and the bridge is still not
  built.
