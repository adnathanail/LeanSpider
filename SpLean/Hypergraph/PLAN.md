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

`toHyp` lives in `Algebraic/` because it mentions `ZX`, which leaves room for
an `Axiomatic/ToHypergraph.lean` later — the long-promised bridge, since a
semantics for `ZXDiagram` is exactly the soundness target the axioms in
`Axiomatic/Rules/` have always lacked.

**`Hypergraph/` importing neither representation is a preference, not a rule.**
The phase type is where it bites: `Hyp` is parameterised over `Φ` with
`[DecidableEq Φ]`, and `Hyp.sem` takes the interpretation `expI : Φ → ℂ` as an
argument, so the folder needs nothing from either half;
`Algebraic/ToHypergraph.lean` instantiates at `AlgPhase` and `AlgPhase.expI`.
That is worth keeping for its own sake — the structure genuinely does not care
what a phase is, and a second lowering from `Axiomatic/` would arrive with a
different one. But if the parameter turns into a tax, importing
`Algebraic.AlgPhase` is an acceptable retreat rather than a breach.

## Phases

**Phase 0 — spike the encoding. DONE.** `Defs.lean`, `Semantics.lean` and
`Algebraic/ToHypergraph.lean` exist; `toHyp` covers all six constructors, and
`sem_toHyp_wire`, `sem_toHyp_zSpider`, `sem_toHyp_wire_compose` are proved with
no `sorry`. What the spike settled:

- **Identification deltas work.** `compose` records `a`'s output wire and `b`'s
  input wire as a pair and renumbers nothing; `Hyp.sem` carries `[a v = a v']`
  per pair. `sem_toHyp_wire_compose` is the test that this does not leave a
  wire summed over freely — it would have come out a factor of two wrong, and
  it does not.
- **Boxes carry their arity.** This is the one thing the spike changed. Legs
  were a `List (Fin wires)`, which made a box's leg tensor land at arity
  `List.length`, so every lemma about it had to transport along
  `List.length_ofFn` — a dependent rewrite in a type index. A `Box` record with
  an `arity : ℕ` field and `legs : Fin arity → Fin wires` removes that
  entirely, and the spider case then goes through on `Fin.addCases` lemmas
  alone.
- **`Fin` vertex ids are fine so far.** `Fin.castAdd`/`Fin.natAdd` embed the
  two halves in `stack` and `compose` and `Fin.addCases` splits the boundary,
  which is the same vocabulary `Algebraic/Semantics.lean` already uses. Revisit
  only if phase 3's `decide` struggles.
- **Still open:** well-formedness (the degree-2 and distinct-boundary
  invariants below) is not stated or enforced anywhere yet, and whether leg
  lists compare up to permutation is now a question for `Iso` in phase 1 —
  with legs as `Fin arity → Fin wires`, that means comparing up to a
  permutation of `Fin arity`.

Two invariants of anything `toHyp` produces, to state in `Defs.lean` when
phase 1 needs them:

- every wire has degree exactly 2, counting boundary ports as ends;
- the input wires are pairwise distinct, and likewise the outputs. (A wire has
  two ends, and no term can make both of them inputs.) So the merge is a
  bijection between two disjoint `m`-element sets, not something messier.

**Phase 1 — isomorphism invariance. DONE.** `Iso.lean` has `Hyp.Rel`, `Iso`,
`Iso.sem_eq`, and the negative test, all with no `sorry`. What it settled:

- **`Iso` had to be up to `Hyp.Rel`, not a plain bijection**, and this is not a
  nicety: in `toHyp Gate.CNOT` the Z spider's input leg *is* the boundary input
  wire, while in `toHyp Gate.CNOT'` the boundary input is a separate wire
  identified with that leg. No bijection matches those two, and they are
  obviously the same diagram. Stating everything up to `Rel` also lets an
  isomorphism relate hypergraphs with different wire counts, which is needed
  the moment one side is composed with a bare `wire`.
- **The proof is one `Fintype.sum_equiv`.** `Hyp.sem_eq_sum_sat` restricts the
  sum to assignments respecting the identifications (the `ids` indicator only
  ever kills terms), and on those the two wire maps *are* mutually inverse, so
  they give an `Equiv` (`Iso.assignEquiv`). Boundary indicators then agree
  because the boundary is fixed, and box products agree box by box via
  `Label.tensor_congr`.
- **Leg lists compare up to permutation**, as anticipated: `Iso.legPerm` gives
  an `Equiv (Fin b₁.arity) (Fin b₂.arity)` per box, and the tensors do not
  notice — that is `zTensor_congr`/`xTensor_congr`/`hadTensor_congr` in
  `Semantics.lean`, stated across two arities rather than as invariance under
  `Equiv.Perm` because that is the shape `Iso` produces. This is where the
  spider symmetry that the term calculus cannot express actually comes from.
- **`boxes` and `ids` became `Fin`-indexed too**, for the reason phase 0 made
  `Box.arity` a field: a `List` puts `List.length` in a type index and every
  lemma then needs a dependent rewrite. Nothing in `Hypergraph/` is a `List`.
- **The negative test has teeth.** `swapHyp` and `parallelHyp` are written by
  hand (`ZX` has no crossing to lower) and `sem_swap_ne_sem_parallel` shows
  their denotations differ, so `not_nonempty_iso_swap_parallel` follows from
  `Iso.sem_eq`. If a future weakening of `Iso` admits an isomorphism between
  them, the file stops compiling.
- **Still open:** well-formedness is still not stated — phase 1 turned out not
  to need it. It is phase 3's `decide` that will care, along with a computable
  replacement for `Relation.EqvGen`, which is a `Prop` and cannot be decided
  as it stands.

**Phase 2 — the lowering theorem. DONE.** `sem_toHyp` is proved for all six
constructors, with no `sorry`, and `ZX.Equiv.of_hyp_iso` — *isomorphic
hypergraphs give equivalent diagrams* — falls out in three lines from it and
`Iso.sem_eq`. What it took:

- **`compose` was the long case, and came out shorter than feared.** The
  identifications composition records are exactly what `ZX.sem`'s `∑ g` ranges
  over: for fixed assignments to the two halves there is at most one `g`
  matching both, and it exists precisely when the identified wires agree. So
  the proof is `Finset.sum_mul_sum`, two `Finset.sum_comm`s to get `g`
  innermost, and `Finset.sum_eq_single` to collapse it.
- **`stack` factors**, via `sum_addCases` for the assignments,
  `forall_fin_add` for the boundary and identification conditions,
  `prod_appendBoxes` for the boxes, and `ite_and_mul` to split each indicator
  of a conjunction into a product so `ring` can finish.
- **Dependent rewriting was the recurring obstacle.** `Box.bits b x` has type
  `Bits b.arity`, so `simp` will not rewrite `b` underneath it — the motive is
  not type correct. The fix is to move the whole `Label.tensor _ b.label
  (b.bits _)` unit at once (`tensor_congr_box`), which is well typed however
  `b` is rewritten. Relatedly, `(Fin.addCases ..).label` does not even
  elaborate when written by hand, so the juxtaposition of two halves' boxes and
  identifications is named (`appendBoxes`, `appendIds`) with `_left`/`_right`
  simp lemmas rather than left as a bare `Fin.addCases`.
- **The X spider needed no new idea**: both sides define X by conjugating Z
  with Hadamards, so `xTensor_addCases` is that definition on either side of
  the lowering, and the work is splitting the conjugating product and the
  summed-over boundary in two.

**Phase 3 — cash it in. HALF DONE.** The certificate route works end to end:
`cnot_cnot_iso` in `SemanticsTesting/10Hypergraph.lean` proves
`Gate.CNOT ≈zx Gate.CNOT'` by exhibiting an isomorphism whose every side
condition is `decide`, and it depends on **no** `sorry` — unlike
`cnot_cnot_rewrite`, which rests on four stubbed rules. What it took:

- **`Hyp.Rel` is a `Prop`, so it is replaced by a computable representative
  map.** `Hyp.rep` (`Decide.lean`) is one pass of quick-find over `ids`, and
  what is proved about it is `H.Rel u (H.rep u)`, hence
  `rep u = rep v → H.Rel u v`. The converse is deliberately *not* proved: a
  certificate is accepted when the representatives agree, so only this
  direction can make the check unsound. Completeness would only ever cost a
  certificate that fails to check.
- **`Iso.ofRepEq`** takes the four pieces of data and restates every `Rel`
  condition as an equality of representatives, all decidable. The two
  `map_rel` fields are the ones worth noting: it is enough to check that each
  *recorded identification* is sent to a related pair, since `Rel` is generated
  by those, and the general statement follows by induction on the derivation.
- **`decide` copes** at this size (8 wires, 2 boxes) without special pleading.

What is left of this phase is the more valuable half: the **general laws**.
`stack_interchange` and friends quantify over arbitrary `a b c d`, so `decide`
has nothing to compute on and `ofRepEq` does not apply — each needs its
isomorphism *constructed*, with the `Rel` conditions proved rather than
checked. `compose_assoc` is the one to try first: the two hypergraphs differ
only in how their wire counts are bracketed, so the wire map is a `Fin.cast`
along `Nat.add_assoc` and nothing else moves. Doing this would discharge the
four stubs in `Rules/Structural.lean` and the eight in `Rules/Yank.lean` from
one mechanism.

**Phase 4 — automation (explicitly out of scope for now).** Searching for the
isomorphism rather than being handed it. A `MetaM` search emitting a
certificate the kernel then checks keeps the trusted core small. Deliberately
last: everything above is useful with the witness supplied by hand.

**Later, not part of this plan.** A normal form that absorbs fusion (connected
same-colour spiders merge) would move fusion into the isomorphism check too.
DPO rewriting sits naturally on this encoding. `Axiomatic/ToHypergraph.lean`
plus the same lowering theorem would give the axioms in `Axiomatic/Rules/` a
soundness target. A `Hyp → Wire.Diagram` lowering would let `#zx` draw one.

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
