# Plan: hypergraph rewriting

Status: **plan only, no code yet.** This file is the brief; delete or fold it
into a `CLAUDE.md` once `SpLean/Hypergraph/` actually holds something.

## The idea

Two ZX terms that denote the same *graph* should be interchangeable, and
proving it should not require a derivation. The route:

1. lower a term to a combinatorial structure that has forgotten how the term
   was bracketed — `toHyp : ZX n m → Hyp`;
2. prove that lowering preserves the denotation — `(toHyp a).sem = a.sem`;
3. prove that isomorphic structures have equal denotations —
   `H₁ ≅ H₂ → H₁.sem = H₂.sem`;
4. conclude: `toHyp a ≅ toHyp b → a ≈zx b`, with scalar `c = 1`.

Steps 2 and 3 are proved once. After that, showing two terms equivalent means
exhibiting an isomorphism, which for closed terms is a finite check.

This is the shape described for VyZX/TensorRocq. **Nobody here has read those
sources closely — check the technique against them before committing** (links
in `IDEAS.md`; the TensorRocq paper is the one to read first). The argument
above stands on its own regardless of whether it matches theirs.

## Why it is worth doing here

`SemanticsTesting/09Rules.lean`'s `cnot_cnot_rewrite` is the motivating
example. Twelve lines of `zx_rw` — bend, split rows into layers, regroup,
interchange, tidy — to prove that two decompositions of *the same graph* agree.
None of those steps says anything about ZX; they are all bookkeeping about how
the term was bracketed. Under this plan that proof becomes an isomorphism
certificate.

What it subsumes: `compose_assoc`, `stack_assoc`, the unit laws,
`stack_interchange`, `stack_compose_below`/`above`, the `nWire` identities, the
snakes and the bends — everything in `Rules/Structural.lean` and
`Rules/Yank.lean`. It also gives **full spider symmetry**, which the bends
cannot: bending only rotates a leg between the two ends, whereas a hypergraph
has no leg order at all.

What it does **not** subsume: fusion, colour change, Hopf, π-copy, state copy,
Euler, self-loops, bialgebra. Those relate *different* graphs and stay as
rules. This is a plan about the structural half of the rule set, not about ZX.

## Why it can work at all

`ZX.sem`'s vertex tensors are already leg-order-agnostic, which is the fact the
whole plan rests on:

- `zSpiderSem φ f g` is `1` when every boundary bit is `false`, `φ.expI` when
  every bit is `true`, `0` otherwise — a function of the *multiset* of incident
  values, and it does not distinguish inputs from outputs;
- `xSpiderSem` is that conjugated by Hadamards on every wire, so likewise;
- `hadSem a b` is symmetric in `a` and `b`.

So a spider is genuinely a symmetric `(n+m)`-leg tensor, and discarding leg
order loses nothing. If a generator is ever added whose tensor is *not*
symmetric (a W node is the standard example — see the last line of
`IDEAS.md`), this plan breaks for that generator and it needs a port graph
rather than a hypergraph.

## The trap

**The isomorphism must fix the boundary pointwise, in order.** An iso that is
free to permute boundary ports proves `swap ≈zx wire ⊗ wire`, which is false.
Every statement below therefore quantifies over isos that are the identity on
`Fin n` inputs and `Fin m` outputs. Write that into the definition of `Iso`
rather than as a side condition, so it cannot be forgotten.

A useful sanity check to keep as a test: the iso relation must **not** identify
`ZX.wire ⊗ ZX.wire` with any diagram that crosses its two wires.

## Where it lives

A new top-level folder, a sibling of `Axiomatic/` and `Algebraic/`:

```
SpLean/Hypergraph.lean             -- aggregator
SpLean/Hypergraph/Defs.lean        -- Vertex, End, Hyp, well-formedness
SpLean/Hypergraph/Semantics.lean   -- Hyp.sem
SpLean/Hypergraph/Iso.lean         -- Iso (boundary-fixing) + sem invariance
SpLean/Hypergraph/Decide.lean      -- certificate checking            [phase 3]
SpLean/Algebraic/ToHypergraph.lean -- toHyp, the lowering theorem, zx_iso_of
```

**`Hypergraph/` imports neither representation**, exactly as `SpLean/Widget.lean`
imports neither: the halves lower *into* it. `toHyp` lives in `Algebraic/`
because it mentions `ZX`. That keeps the existing rule intact (check with
`grep -rh "^import" SpLean/Hypergraph/`) and leaves room for an
`Axiomatic/ToHypergraph.lean` later — which is the long-promised bridge, since
a semantics for `ZXDiagram` is what the axioms in `Axiomatic/Rules/` have
always lacked as a soundness target.

Consequence: the phase type. `Hypergraph/` cannot import `AlgPhase`, and
copying the whole of `Algebraic/AlgPhase/` into it is too much to duplicate
(unlike `SpiderColor`/`AlgSpColor`, which was three lines). **Recommendation:
parameterise.** `Hyp Φ` carries labels over an arbitrary phase type with
`[DecidableEq Φ]`, and `Hyp.sem` takes the interpretation `(expI : Φ → ℂ)` as
an argument. `Algebraic/ToHypergraph.lean` instantiates it at `AlgPhase` and
`AlgPhase.expI`. Costs a parameter everywhere; keeps the folder honest.

## Encoding

This is the decision that makes or breaks the work, so spike it first
(phase 0).

Sketch to start from:

```lean
inductive Vertex (Φ : Type) | spider (c : Colour) (φ : Φ) | hadamard
inductive End | bnd (side : Bool) (i : ℕ) | vtx (v : ℕ)

structure Hyp (Φ : Type) where
  inputs   : ℕ
  outputs  : ℕ
  verts    : List (Vertex Φ)          -- indices are vertex ids
  edges    : List (End × End)         -- indices are edge ids; ends unordered
```

Notes on why, and what to watch:

- **Wires are edges, not vertices.** `ZX.wire` lowers to a single edge from
  input 0 to output 0 and contributes no vertex; `ZX.empty` to nothing. That is
  what makes the unit laws (`.empty ⊗ a`) and `nWire_one` come out as
  isomorphisms rather than needing proof. (Note this is the opposite of
  `Algebraic/Visualize.lean`, which deliberately keeps `wire` as a real node so
  the *drawing* has something to put in a box. Different concern; don't
  conflate them.)
- **Parallel edges and self-loops must both work** — Hopf needs the first, and
  `Rules/SelfLoop.lean` the second. Indexing edges by position gives both for
  free: two edges with the same pair of ends are distinct, and an edge with
  both ends at one vertex is a loop.
- **Edge ends are unordered.** Either use `Sym2 End`, or keep the pair ordered
  and let `Iso` match an edge to a flipped one. Pick one in phase 0; `Sym2` is
  cleaner to state with and clunkier to compute with.
- **Well-formedness**: every boundary port is an end of exactly one edge, and
  every `vtx v` is in range. Needed for `sem` to mean anything. Either a `WF`
  predicate proved for everything `toHyp` produces, or an encoding that makes
  it impossible; decide in phase 0, but do not let `sem` be defined on
  ill-formed values without noticing.
- **`compose` is where the work is.** Gluing `a`'s outputs to `b`'s inputs
  merges each pair of edges that met at the shared boundary into one edge, which
  renumbers everything. Give it its own API (`Hyp.glue`) with its own lemma, and
  choose the encoding to make it cheap — if gluing is painful, the encoding is
  wrong. A partition-of-ports (union-find) representation is the alternative if
  the edge-list one fights back.

## Semantics

Assign a Bool to every edge; each vertex contributes its tensor applied to the
values on its incident edges; boundary edges are pinned by `f` and `g`:

```lean
noncomputable def Hyp.sem (expI : Φ → ℂ) (H : Hyp Φ) (f : Wires H.inputs) (g : Wires H.outputs) : ℂ :=
  ∑ a : Fin H.edges.length → Bool,
    (boundary indicator for f and g) * ∏ v, vertexTensor expI (H.label v) (incident values of a at v)
```

`Wires` is `Fin n → Bool`, as in `Algebraic/Semantics.lean` — the same
"boundary tensor" convention, which is exactly why this is tractable: the
module CLAUDE.md's line about permuting wires being "reindexing a sum, i.e. an
`Equiv`, not a matrix conjugation" is the promise this cashes in.

## Phases

**Phase 0 — spike the encoding.** `Defs.lean` + `Semantics.lean` + prove
`(toHyp ZX.wire).sem = ZX.wire.sem` and the same for one spider and for
`wire ≫ wire`. Acceptance: those three go through without fighting the
encoding. If `compose` already hurts here, change the encoding now, not later.

**Phase 1 — isomorphism invariance.** `Iso.lean`: boundary-fixing iso, and
`H₁ ≅ H₂ → H₁.sem = H₂.sem`, by reindexing the edge-sum and the vertex-product
along the two bijections (`Equiv.sum_comp`, `Finset.prod_bij`). Independent of
phase 2, so it can be done in parallel. Acceptance: the theorem, plus the
`swap`-shaped negative test above.

**Phase 2 — the lowering theorem.** `Algebraic/ToHypergraph.lean`:
`toHyp` by structural recursion, then `∀ a : ZX n m, (toHyp a).sem = a.sem` by
induction. `empty`/`wire`/`hadamard`/`spider` are immediate; `stack` is a
disjoint union with the boundary split (mirroring the `Fin.castAdd`/`natAdd`
split in `ZX.sem`); `compose` is the glue, and the sum over the shared boundary
in `ZX.sem` becomes the sum over the newly-internal edges. Acceptance: the
theorem, with `compose` as the only long proof.

**Phase 3 — the bridge, and cash it in.** `zx_iso_of : toHyp a ≅ toHyp b → a ≈zx b`
(one line from phases 1 and 2). Then:
- *Concrete goals*: supply the iso as an explicit certificate and discharge the
  conditions with `decide`. First target: `cnot_cnot_equiv` by certificate,
  replacing the twelve-line derivation — keep both, the derivation is a
  regression test for `zx_rw`.
- *General laws*: `stack_interchange` and friends are quantified over arbitrary
  `a b c d`, so `decide` cannot touch them. Each needs its iso *constructed*
  generically. This is more work but it is the real prize: it would discharge
  the four stubs in `Rules/Structural.lean` and the eight in `Rules/Yank.lean`
  from one mechanism instead of twelve semantic proofs.

**Phase 4 — automation (explicitly out of scope for now).** Searching for the
isomorphism rather than being handed it. A `MetaM` search emitting a
certificate that the kernel checks keeps the trusted core small. Deliberately
last: everything above is useful with the witness supplied by hand.

**Later, not part of this plan.** A hypergraph normal form that absorbs fusion
(connected same-colour spiders merge) would move fusion into the iso check too.
`Axiomatic/ToHypergraph.lean` plus the same lowering theorem would give the
axioms in `Axiomatic/Rules/` a soundness target. A `Hyp → Wire.Diagram`
lowering would let `#zx` draw one.

## Notes on interaction with what exists

- **This does not need `swap`**, and does not add it. The ADT still generates
  only planar terms; `toHyp` is defined on what can be written. But it makes
  adding `swap` *cheap later*: a swap contributes no vertex and no edge, only a
  change in which boundary port an edge ends at — so its lowering is trivial
  and the invariance theorem covers it unchanged. Doing the hypergraph layer
  first is the right order.
- **Scalars.** Isomorphism gives equality on the nose, so `zx_iso_of` yields
  `c = 1`. If `ZX.Equiv` is ever changed to track its scalar (the `TODO` in
  `Equiv.lean`), this route keeps working and reports `1`.
- **`ZX.cast`.** A cast should lower to the *same* hypergraph as the diagram
  underneath it, since it changes no vertex and no edge. Worth an explicit
  lemma (`toHyp (ZX.cast hn hm a) = toHyp a`), because it makes every arity
  cast disappear at the hypergraph level — which is a second, quieter payoff of
  this plan.
