# Plan: hypergraph rewriting

Status: **plan only, no code yet.** This file is the brief; delete it or fold
it into a `CLAUDE.md` once `SpLean/Hypergraph/` holds something.

## The idea

Two ZX terms that denote the same *graph* should be interchangeable, and
proving it should not require a derivation. The route:

1. lower a term to a combinatorial structure that has forgotten how the term
   was bracketed — `toHyp : ZX n m → Hyp Φ n m`;
2. prove that lowering preserves the denotation — `(toHyp a).sem = a.sem`;
3. prove that isomorphic structures have equal denotations —
   `H₁ ≅ H₂ → H₁.sem = H₂.sem`;
4. conclude: `toHyp a ≅ toHyp b → a ≈zx b`, with scalar `c = 1`.

Steps 2 and 3 are proved once. After that, showing two terms equivalent means
exhibiting an isomorphism, which for closed terms is a finite check.

This is the shape described for VyZX/TensorRocq. **Nobody here has read those
sources closely — check the technique against them before committing** (links
in `IDEAS.md`; the TensorRocq paper first). The argument stands on its own
either way.

## Why it is worth doing here

`SemanticsTesting/09Rules.lean`'s `cnot_cnot_rewrite` is the motivating
example: twelve lines of `zx_rw` — bend, split rows into layers, regroup,
interchange, tidy — to prove that two decompositions of *the same graph* agree.
Not one of those steps says anything about ZX; they are all bookkeeping about
how the term was bracketed. Under this plan that proof becomes an isomorphism
certificate.

What it subsumes: `compose_assoc`, `stack_assoc`, the unit laws,
`stack_interchange`, `stack_compose_below`/`above`, the `nWire` identities, the
snakes and the bends — everything in `Rules/Structural.lean` and
`Rules/Yank.lean`. It also gives **full spider symmetry**, which the bends
cannot: bending only rotates a leg between the two ends of a spider, whereas a
hyperedge has no leg order at all.

What it does **not** subsume: fusion, colour change, Hopf, π-copy, state copy,
Euler, self-loops, bialgebra. Those relate *different* graphs and stay as
rules. This is a plan about the structural half of the rule set, not about ZX.

## The encoding: wires are vertices, generators are hyperedges

The structure is the **incidence dual** of the picture the renderer draws:

- a **vertex** is a *wire* — including the implied ones. `Z ≫ Z` has a wire
  between the two spiders that the term never names, and it is a vertex;
- a **hyperedge** is a *generator* — a spider or a Hadamard — labelled, and
  incident to the wires on its legs;
- the **boundary** is two lists of vertices: which wire each input and each
  output port is.

Sketch:

```lean
inductive Label (Φ : Type) | spider (c : Colour) (φ : Φ) | hadamard

structure Hyp (Φ : Type) (n m : ℕ) where
  wires   : ℕ                                     -- vertex ids are `Fin wires`
  boxes   : List (Label Φ × List (Fin wires))     -- hyperedges: label + legs
  inputs  : Fin n → Fin wires
  outputs : Fin m → Fin wires
```

Why this way round, and what falls out of it:

- **`compose` is a vertex merge.** `a ≫ b` is the disjoint union with `a`'s
  output vertex `i` identified with `b`'s input vertex `i` — a quotient of the
  vertex set, i.e. a pushout. Compare the alternative (generators as vertices,
  wires as edges), where composing has to *merge edges* and renumber
  everything. This is the presentation DPO rewriting is stated in, so the
  "double pushout rewriting" line in `IDEAS.md` continues naturally from here
  rather than needing a different structure.
- **`ZX.wire` is one vertex and no hyperedges**, with `inputs = [v]` and
  `outputs = [v]` — so the boundary maps are *not* injective in general, and
  must not be assumed to be. `ZX.empty` is nothing at all. That is what makes
  the unit laws (`.empty ⊗ a`) and `nWire_one` come out as isomorphisms
  rather than needing proof.
- **Self-loops and parallel wires are automatic.** A spider with a self-loop is
  a hyperedge whose leg list mentions one vertex twice; two spiders joined by
  two wires are two hyperedges sharing two vertices. Both are needed —
  `Rules/SelfLoop.lean` and Hopf respectively.
- **Arity-index `Hyp` by `n` and `m`.** Then `toHyp : ZX n m → Hyp Φ n m` and
  `(toHyp a).sem = a.sem` state without a cast in sight. The `Fin (n + p)`
  bookkeeping in `stack` is the same `castAdd`/`natAdd` split that
  `Algebraic/Semantics.lean` already does, so it is no new problem.
- **Every vertex has degree exactly 2** in anything `toHyp` produces, counting
  boundary ports as ends, because a wire in a term has two ends. Worth stating
  as a well-formedness invariant even though `sem` does not need it: it is a
  cheap sanity check on the lowering, and it bounds the isomorphism search
  later. (Wires of higher degree are what the Frobenius presentation allows
  when spiders are *quotiented into* the wiring; here spiders stay explicit as
  hyperedges, so degree stays 2.)
- **Leg lists: ordered or not?** Stored as a `List` above, but every current
  label is symmetric, so the isomorphism should compare leg lists **up to
  permutation**. This is exactly where the W-node question at the bottom of
  `IDEAS.md` lands: a generator whose tensor is not symmetric in its legs needs
  ordered ports (a port hypergraph) and would have to restrict this. Decide in
  phase 0 and write the reason down.
- `Fin wires` inside the structure is dependent and pleasant to reason about
  but awkward to `decide` with; ℕ ids plus a well-formedness bound are the
  alternative. Settle this in phase 0.

## Why it can work at all

`ZX.sem`'s generator tensors are already leg-order-agnostic, which is the fact
the whole plan rests on:

- `zSpiderSem φ f g` is `1` when every boundary bit is `false`, `φ.expI` when
  every bit is `true`, `0` otherwise — a function of the *multiset* of incident
  values, which does not even distinguish inputs from outputs;
- `xSpiderSem` is that conjugated by Hadamards on every wire, so likewise;
- `hadSem a b` is symmetric in `a` and `b`.

So a spider is genuinely a symmetric `(n+m)`-leg tensor, and turning it into a
hyperedge with an unordered leg list loses nothing.

## Semantics

A vertex is a wire, so it carries one bit. Assign a Bool to every vertex, let
each hyperedge contribute its tensor applied to the bits on its legs, pin the
boundary vertices with `f` and `g`, and sum:

```lean
noncomputable def Hyp.sem (expI : Φ → ℂ) (H : Hyp Φ n m) (f : Wires n) (g : Wires m) : ℂ :=
  ∑ a : Fin H.wires → Bool,
    (if (∀ i, a (H.inputs i) = f i) ∧ (∀ j, a (H.outputs j) = g j) then 1 else 0) *
      ∏ b ∈ H.boxes, boxTensor expI b.1 (b.2.map a)
```

Two checks that this is the right definition, both worth writing as tests:

- `ZX.wire`: one vertex, no hyperedges, so the sum collapses to
  `if f 0 = g 0 then 1 else 0` — `ZX.sem`'s wire clause exactly. Note this
  needs the boundary maps to be allowed to coincide.
- `Z ≫ Z`: three vertices, two hyperedges, and the sum over the middle vertex
  is precisely `ZX.sem`'s `∑ g, a.sem f g * b.sem g h`. That correspondence —
  *the vertices that composition merged are the ones that get summed over* — is
  the whole proof of the `compose` case, and it is why this encoding is the one
  to use.

`Wires` is `Fin n → Bool` as in `Algebraic/Semantics.lean`. Keeping that
convention is what makes this tractable: the module CLAUDE.md's line about
permuting wires being "reindexing a sum, i.e. an `Equiv`, not a matrix
conjugation" is the promise this cashes in.

## The trap

**The isomorphism must fix the boundary pointwise, in order** — `iso (H₁.inputs i) = H₂.inputs i`
and the same for outputs. An iso free to permute boundary ports proves
`swap ≈zx wire ⊗ wire`, which is false. Put it in the definition of `Iso`
rather than carrying it as a side condition, so it cannot be forgotten, and
keep "`wire ⊗ wire` is not isomorphic to a crossing" as a standing test.

## Where it lives

A new top-level folder, a sibling of `Axiomatic/` and `Algebraic/`:

```
SpLean/Hypergraph.lean             -- aggregator
SpLean/Hypergraph/Defs.lean        -- Label, Hyp, well-formedness
SpLean/Hypergraph/Semantics.lean   -- Hyp.sem
SpLean/Hypergraph/Iso.lean         -- Iso (boundary-fixing) + sem invariance
SpLean/Hypergraph/Decide.lean      -- certificate checking            [phase 3]
SpLean/Algebraic/ToHypergraph.lean -- toHyp, the lowering theorem, zx_iso_of
```

`toHyp` lives in `Algebraic/` because it mentions `ZX`.

**`Hypergraph/` importing neither representation is a preference, not a rule.**
The phase type is where it bites: `Hyp` is parameterised over `Φ` with
`[DecidableEq Φ]`, and `Hyp.sem` takes the interpretation `expI : Φ → ℂ` as an
argument, so the folder needs nothing from either half;
`Algebraic/ToHypergraph.lean` instantiates at `AlgPhase` and `AlgPhase.expI`.
That is worth keeping for its own sake — the structure genuinely does not care
what a phase is. But if the parameter turns into a tax, importing
`Algebraic.AlgPhase` is an acceptable retreat rather than a breach.

## Phases

**Phase 0 — spike the encoding.** `Defs.lean` + `Semantics.lean`, and prove
`(toHyp ZX.wire).sem = ZX.wire.sem`, the same for one spider, and for
`wire ≫ wire`.

The decision this hangs on is **how the vertex merge is represented**. Saying
"identify `a`'s output vertex `i` with `b`'s input vertex `i`" is three
different pieces of Lean, and the choice reaches all the way to phase 3:

- *`Fin w` + compaction* — merge and renumber to a normal form. Concrete and
  decidable; `Fin` arithmetic with subtraction is miserable.
- *`Fin w` + identification deltas* — do not renumber. Keep both vertices and
  let `sem` carry a `[a v = a v']` factor per identified pair, which exactly
  cancels the spurious factor of `2` a now-dead vertex would contribute.
  Everything stays computable; the cost is that `Hyp` is not in normal form, so
  `Iso` has to work up to the identifications (or normalise once at the top).
- *Bundled `V : Type` + a real quotient* — cleanest to prove with, and `decide`
  in phase 3 gets awkward, since the vertex type may be a quotient.

**The trap either way:** if merging leaves vertices that nothing mentions and
the sum still ranges over them, `sem` gains a factor of `2` per dead vertex and
the lowering theorem stops holding on the nose. Whichever representation is
picked has to answer for that, and the `wire ≫ wire` test is what catches it —
it is the smallest term where a vertex is merged at all.

Two invariants of anything `toHyp` produces, worth stating in `Defs.lean`
because the merge relies on the second:

- every vertex has degree exactly 2, counting boundary ports as ends;
- the input vertices are pairwise distinct, and likewise the outputs. (A wire
  has two ends, and no term can make both of them inputs.) So the merge is a
  bijection between two disjoint `m`-element sets, not something messier.

Also settle here: `Fin` vs ℕ vertex ids, leg lists up to permutation, and how
well-formedness is carried. Acceptance: the three lemmas go through without
fighting the definitions. If the vertex merge already hurts, change it now.

**Phase 1 — isomorphism invariance.** `Iso.lean`: the boundary-fixing
isomorphism, and `H₁ ≅ H₂ → H₁.sem = H₂.sem`, by reindexing the vertex-sum and
the hyperedge-product along the two bijections (`Equiv.sum_comp`,
`Finset.prod_bij`). Independent of phase 2 — can be done in parallel.
Acceptance: the theorem, plus the `swap`-shaped negative test.

**Phase 2 — the lowering theorem.** `Algebraic/ToHypergraph.lean`: `toHyp` by
structural recursion, then `∀ a : ZX n m, (toHyp a).sem = a.sem` by induction.
`empty`/`wire`/`hadamard`/`spider` are immediate; `stack` is a disjoint union
with the boundary split; `compose` is the vertex merge, and the sum over the
shared boundary in `ZX.sem` becomes the sum over the merged vertices.
Acceptance: the theorem, with `compose` the only long proof.

**Phase 3 — the bridge, and cash it in.**
`zx_iso_of : toHyp a ≅ toHyp b → a ≈zx b`, one line from phases 1 and 2. Then:

- *Concrete goals*: supply the isomorphism as an explicit certificate and
  discharge its conditions by `decide`. First target: `cnot_cnot_equiv` by
  certificate, replacing the twelve-line derivation — keep both, since the
  derivation is a regression test for `zx_rw`.
- *General laws*: `stack_interchange` and friends quantify over arbitrary
  `a b c d`, so `decide` has nothing to compute on; each needs its isomorphism
  *constructed* generically. More work, but it is the real prize — it would
  discharge the four stubs in `Rules/Structural.lean` and the eight in
  `Rules/Yank.lean` from one mechanism instead of twelve semantic proofs.

**Phase 4 — automation (explicitly out of scope for now).** Searching for the
isomorphism rather than being handed it. A `MetaM` search emitting a
certificate the kernel then checks keeps the trusted core small. Deliberately
last: everything above is useful with the witness supplied by hand.

**Later, not part of this plan.** A normal form that absorbs fusion (connected
same-colour spiders merge) would move fusion into the isomorphism check too.
DPO rewriting sits naturally on this encoding. A `Hyp → Wire.Diagram` lowering
would let `#zx` draw one.

## Notes on interaction with what exists

- **This does not need `swap`**, and does not add it — the ADT still generates
  only planar terms. But it makes adding one *cheap later*, and this encoding
  makes it cheaper still: a swap is two vertices, no hyperedges, and
  `outputs` the reverse of `inputs`. Nothing about `sem` or the invariance
  theorem changes. Do the hypergraph layer first.
- **Scalars.** Isomorphism gives equality on the nose, so `zx_iso_of` yields
  `c = 1`. If `ZX.Equiv` is ever changed to track its scalar (the `TODO` in
  `Equiv.lean`), this route keeps working and reports `1`.
- **`ZX.cast`** should lower to the *same* hypergraph as the diagram
  underneath, since it changes no wire and no generator. Worth an explicit
  lemma (`toHyp (ZX.cast hn hm a) = toHyp a`): it makes every arity cast vanish
  at the hypergraph level, which is a second, quieter payoff.
