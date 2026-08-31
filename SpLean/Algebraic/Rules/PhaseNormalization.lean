import SpLean.Algebraic.Equiv
import SpLean.Algebraic.AlgPhase
import SpLean.Algebraic.Reassoc

namespace SpLean.Algebraic

/-- Replace a spider's phase by its normal form in `[0, 2π)`.

The rule is `spider_congr` applied to `AlgPhase.expI_normalize`: normalizing
moves the representative but not the denotation, so the two spiders are equal
on the nose (`c = 1`), not merely proportional.

For a *closed* phase the normal form still has to be computed — `normalize
(2π)` is not syntactically `0` — and `decide` cannot do it, since `Int.floor`
on `ℚ` does not reduce in the kernel. Follow the rewrite with
`norm_num [AlgPhase.normalize, AlgPhase.red]`. -/
@[zx_reassoc]
theorem spider_normalize (c : AlgSpColor) (n m : ℕ) (α : AlgPhase) :
    ZX.spider c n m α ≈zx ZX.spider c n m (AlgPhase.normalize α) :=
  ZX.Equiv.spider_congr c n m (AlgPhase.expI_normalize α).symm

end SpLean.Algebraic
