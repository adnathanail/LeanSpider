- Better equality checking
    - Simplify to canonical form?
    - Conversion to matrices?
- Simplification routines as tactics
- To/from circuit form
- Is the custom insertion sort slow?
- Interactive rewrites
- Prove rewrites
- Add normal forms
- Replace the various individual tactics with a single tactic with args
    - Can we use the existing rw tactic? And just pass it theorems?
- Make the widget display current proof state at cursor position
- Prove 2 CNOT versions are equal
- Prove scalar universality
- Implement the rest of the semantics (X/H/etc.)

- Try to simplify to a single rewrite tactic
- Try to prove a very simple spider fusion
- Read the hypergraphs paper again (with the help of AI)

- double push out rewriting
- hypergraph rewriting: built, see `SpLean/Hypergraph/CLAUDE.md` (rewriting itself still to do)

Things to prove:
- local complementation always terminates
- spider fusion always terminates

Things to research
- xiaoning bian
- minicrypt
    - leo collison
    - diagrams formalisation
- chyp

Lean things to play with:
- [aesop](https://github.com/leanprover-community/aesop)

- Add Dirac semantics for neater proofs?


- TensorRocq: Enabling diagrammatic reasoning in Rocq
    - https://arxiv.org/pdf/2604.17592
    - https://github.com/inQWIRE/TensorRocq
- VyZX: Formal Verification of a Graphical Quantum Language
    - https://arxiv.org/abs/2311.11571
    - https://github.com/inQWIRE/VyZX
- String Diagram Rewrite Theory II: Rewriting with Symmetric Monoidal Structure
    - https://arxiv.org/pdf/2104.14686
    - Frobenius algebra
    - monads provide a powerful theory for principled and compositional definitions of denotational semantics
    - algebraic theories are particularly useful in the development of formal and principled approaches to operational semantics
    - PROPs: a particularly simple family of symmetric strict monoidal categories
    - The notion of algebraic theory here is that of symmetric monoidal theory, with the essential difference being that the underlying assumption of Cartesianity is discarded
    - Lawvere theories (Cartesian PROPs)
- ZX-Calculus and Extended Hypergraph Rewriting Systems I: A Multiway Approach to Categorical Quantum Information Theory
    - https://arxiv.org/pdf/2010.02752
    - Lots of physics, category theory, and quite unhelpful diagrams
    - Sequel https://arxiv.org/pdf/2103.15820

https://github.com/inQWIRE/LeanQuantum

https://github.com/tannerduve/zxLean/blob/main/ZxCalculus/MultiQubit/DenotationalSemantics.lean

https://github.com/Timeroot/Lean-QuantumInfo
https://github.com/leanprover-community/physlib

Things to ask the Chicagoans:
- When indicator function vs dirac notation
- Do hypergraphs only work for symmetric diagrams? Do we need port graphs for W nodes

To do:
- https://arxiv.org/pdf/1812.09114
    - Minimal axiomatisation of ZX
    - Has complete inductive definition of diagrams
    - Nice statement of theora
    - Published 2018 - investigate what has changed in the field
    - Different shortcodes for rules
- Play with Quantomatic
- Sums of ZX diagrams
    - https://link.springer.com/chapter/10.1007/978-3-031-57228-9_7
        - Full book: Enriching Diagrams with Algebraic Operations
    - https://arxiv.org/pdf/2204.01307v2
        - Notation for linear combinations of diagrams
        - Different shortcodes for rules
- https://quantum-journal.org/papers/q-2024-10-04-1491/pdf/
    - Integrating and differentiating ZX
- John's thesis

## Mathlib.CategoryTheory

https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Monoidal/Category.html
Proving a `MonoidalCategory` instance gives:
- Whiskering and interchange laws
- `coherence`/`pure_coherence` tactic
    - closes goals with different bracketing of same composite
    - Mac Lane coherence
    - Only associators, unitors, whiskering. Not braiding.
- `ZX.sem` can be marked as a `MonoidalFunctor`/`LaxMonoidalFunctor` into a Mathlib `MonoidalCategory` of linear maps
- `Mathlib.Tactic.Widget.StringDiagram` renders monoidal-category goals as string diagrams

Symmetry (swap/permutation of wires) needs `BraidedCategory`/`SymmetricCategory`, with less builtins from Mathlib

Nothing provided for Dagger

