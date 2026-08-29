import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Combinators

namespace SpLean.Algebraic

/-- Self-loop on a Z spider vanishes. -/
theorem zSpider_self_loop (n m : ℕ) (α : AlgPhase) :
    (ZX.spider .Z n (m + 2) α ≫ (ZX.nWire m ⊗ ZX.cap)) ≈zx ZX.spider .Z n m α := by
  sorry

/-- Self-loop through a Hadamard on a Z spider vanishes and adds π to the phase. -/
theorem zSpider_hadamard_self_loop (n m : ℕ) (α : AlgPhase) :
    (ZX.spider .Z n (m + 2) α ≫ (ZX.nWire m ⊗ (ZX.hadamard ⊗ ZX.wire)) ≫ (ZX.nWire m ⊗ ZX.cap))
      ≈zx ZX.spider .Z n m (α + π) := by
  sorry

/-- A plain self-loop on an X spider vanishes. The cap has to be an X cap:
closing two legs of an X spider with a *Z* cap is a Hopf redex
(`Rules/Hopf.lean`), not a self-loop. -/
theorem xSpider_self_loop (n m : ℕ) (α : AlgPhase) :
    (ZX.spider .X n (m + 2) α ≫ (ZX.nWire m ⊗ ZX.capX)) ≈zx ZX.spider .X n m α := by
  sorry

/-- A self-loop through a Hadamard on an X spider vanishes and adds π to the
phase. -/
theorem xSpider_hadamard_self_loop (n m : ℕ) (α : AlgPhase) :
    (ZX.spider .X n (m + 2) α ≫ (ZX.nWire m ⊗ (ZX.hadamard ⊗ ZX.wire))
        ≫ (ZX.nWire m ⊗ ZX.capX))
      ≈zx ZX.spider .X n m (α + π) := by
  sorry

end SpLean.Algebraic
