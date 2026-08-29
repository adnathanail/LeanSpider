import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Combinators

/-!
# The Hopf rule

Two spiders of *opposite* colour joined by two wires come apart: the pair is
equivalent to a cap followed by a cup, i.e. to nothing connecting the two
halves at all. It is the rule that "disconnects" a diagram, and the reason
`Rules/SpiderFusion.lean`'s fusion is stated for same-colour spiders only.

Unlike bialgebra (`Rules/Bialgebra.lean`) this one is statable here: the two
connecting wires are parallel, so no crossing is needed.

Both connecting wires are plain, not Hadamard, so the phases have to be zero —
`spider .Z 1 2 π ≫ spider .X 2 1` is not a Hopf redex.
-/

namespace SpLean.Algebraic

/-- Hopf: a phase-free Z spider and X spider joined by two wires disconnect. -/
theorem hopf_ZX :
    (ZX.spider .Z 1 2 ≫ ZX.spider .X 2 1) ≈zx (ZX.spider .Z 1 0 ≫ ZX.spider .X 0 1) := by
  sorry

/-- Hopf, colours swapped. -/
theorem hopf_XZ :
    (ZX.spider .X 1 2 ≫ ZX.spider .Z 2 1) ≈zx (ZX.spider .X 1 0 ≫ ZX.spider .Z 0 1) := by
  sorry

/-- The Hopf rule at general arity: the two connecting wires disconnect
whatever else the two spiders are attached to. `hopf_ZX` is its `n = m = 1`
instance, kept separately because that is the shape the rule is usually written
in and the one a first proof should target. -/
theorem hopf_ZX_n (n m : ℕ) :
    (ZX.spider .Z n 2 ≫ ZX.spider .X 2 m) ≈zx (ZX.spider .Z n 0 ≫ ZX.spider .X 0 m) := by
  sorry

end SpLean.Algebraic
