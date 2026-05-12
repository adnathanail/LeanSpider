import LeanSpider.Algebraic.ZX
import LeanSpider.Algebraic.Visualize
-- import LeanSpider.Algebraic.Semantics

open LeanSpider.Algebraic

def GateCNOT : ZX 2 2 := (.spider .Z 1 2 ⊗ .wire) × (.wire ⊗ .spider .X 2 1)
#html GateCNOT.toHtml

-- TODO
-- def GateCNOT2 : ZX 2 2 := (.wire ⊗ .spider .X 1 2) × (.spider .Z 2 1 ⊗ .wire)
-- #html GateCNOT2.toHtml

-- -- WIP: needs real `stack`/`X-spider` semantics first; see Algebraic/CLAUDE.md.
-- theorem x : GateCNOT ≃ZX GateCNOT2 := by
--   show _ = _
--   unfold ZX.sem
--   sorry


def GateNOTC : ZX 2 2 := (.spider .X 1 2 ⊗ .wire) × (.wire ⊗ .spider .Z 2 1)
#html GateNOTC.toHtml

def GateCX : ZX 2 2 :=
  (
    (.spider .Z 1 2 ⊗ .wire) ×
    (.wire ⊗ .hadamard ⊗ .wire)
  ) ×
  (.wire ⊗ .spider .Z 2 1)
#html GateCX.toHtml
