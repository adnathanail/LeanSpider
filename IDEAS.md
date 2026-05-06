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


- Make it impossible for phases to have denominator 0
- Add Dirac semantics for neater proofs?