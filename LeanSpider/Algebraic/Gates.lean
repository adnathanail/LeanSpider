import LeanSpider.Algebraic.ZX
import LeanSpider.Algebraic.Visualize

open LeanSpider.Algebraic

def GateCNOT : ZX 2 2 := (.spider .Z 1 2 ⊗ .wire) × (.wire ⊗ .spider .X 2 1)
#html GateCNOT.toHtml

def GateNOTC : ZX 2 2 := (.spider .X 1 2 ⊗ .wire) × (.wire ⊗ .spider .Z 2 1)
#html GateNOTC.toHtml

def GateCX : ZX 2 2 :=
  (
    (.spider .Z 1 2 ⊗ .wire) ×
    (.wire ⊗ .hadamard ⊗ .wire)
  ) ×
  (.wire ⊗ .spider .Z 2 1)
#html GateCX.toHtml
