# Next steps

Written at the end of the `hypergraphs` branch, when the hypergraph layer was
finished end to end (encoding → semantics → isomorphism invariance → lowering →
certificate → search → `zx_iso`). Module detail lives in
`SpLean/Hypergraph/CLAUDE.md` and `SpLean/Algebraic/CLAUDE.md`; this file is
only about what to do next.

## Settled since: `swap`

This file originally opened by asking whether to add a crossing, since without
one `ZX` generates only *planar* diagrams. `main` has since answered it: `ZX`
now has a `swap : ZX 2 2` constructor with its `ZX.sem` clause, layout and
rendering, and strong complementarity is stated and proved over it
(`Rules/StrongComplementarity.lean`). On merging, `toHyp` gained the matching
clause — two vertices, no hyperedges, `outputs` the reverse of `inputs` — and
`sem_toHyp` its case; `Iso.sem_eq` and the certificate path needed no change,
and `zx_iso` handles crossings (see the `swap` tests in
`SemanticsTesting/10Hypergraph.lean`).

What remains of the old concern:

- **Only a single swap, not a general permutation.** Wider permutations are
  built from `swap` and wires; a `perm : Equiv.Perm (Fin n) → ZX n n` would
  still be the cleaner statement for `n`-ary strong complementarity.
- **Spider symmetry is still not a rule.** The `bend_*` rules rotate a leg
  between the two ends of a spider; permuting two adjacent legs is now
  *statable* with `swap` but not yet stated. (The hypergraph layer has full
  symmetry, since a hyperedge has no leg order.)
- **`Hyp → ZX` synthesis does not exist.** Every hypergraph now has *some*
  term, but nothing produces it. See option B.

## Option A: automatic rebracketing (the near one)

A tactic — `zx_apply spider_fusion_Z_one_wire`, say — that searches the
hypergraph for a rule's redex, works out a bracketing that exposes it, proves *that* with the
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

**The obstacle is getting back to a term.** With `swap` every hypergraph has
one, but there is no synthesis to find it; the alternative is to keep every
*stated* equivalence between real terms and use the hypergraph purely as the
engine. Worth deciding explicitly rather than discovering halfway.

## Smaller wins, any time

- **The remaining rule stubs** (`grep -rn sorry SpLean/Algebraic/Rules/`:
  Hopf, spectator fusion, the four bends). `11Ex37.lean` proves concrete
  instances of spectator fusion by `sum_wires2` plus a case split, so those
  are decent templates.
