- Better equality checking
    - Simplify to canonical form?
    - Conversion to matrices?
- Simplification routines as tactics
- To/from circuit form
- Is the custom insertion sort slow?
- Better layouts
    - _auto_layout skips vertices unreachable from inputs (zxRender.py ~line 100)
        - The BFS starts from inputs — disconnected spiders get no row/qubit assignment and default to position 0, causing visual overlap.
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

Things to prove:
- local complementation always terminates
- spider fusion always terminates

Things to research
- xiaoning bian
- minicrypt
    - leo collison
    - diagrams formalisation
- chyp


- Add Dirac semantics for neater proofs?


- TensorRocq: Enabling diagrammatic reasoning in Rocq
    - https://arxiv.org/pdf/2604.17592
- VyZX: Formal Verification of a Graphical Quantum Language
    - https://arxiv.org/abs/2311.11571
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