import SpLean.Algebraic.ZX

open SpLean.Algebraic

namespace SpLean.Algebraic.Gate

abbrev I : ZX 1 1 := .spider .Z 1 1
abbrev I_X : ZX 1 1 := .spider .X 1 1

abbrev T : ZX 1 1 := .spider .Z 1 1 (π/4)
abbrev S : ZX 1 1 := .spider .Z 1 1 (π/2)
abbrev Z : ZX 1 1 := .spider .Z 1 1 π

abbrev X : ZX 1 1 := .spider .X 1 1 π

abbrev CNOT : ZX 2 2 := (.spider .Z 1 2 ⊗ .wire) ≫ (.wire ⊗ .spider .X 2 1)
abbrev CNOT' : ZX 2 2 := (.wire ⊗ .spider .X 1 2) ≫ (.spider .Z 2 1 ⊗ .wire)
abbrev NOTC : ZX 2 2 := (.spider .X 1 2 ⊗ .wire) ≫ (.wire ⊗ .spider .Z 2 1)

abbrev CX : ZX 2 2 := (
    (.spider .Z 1 2 ⊗ .wire) ≫
    ((.wire ⊗ .hadamard) ⊗ .wire)
  ) ≫
  (.wire ⊗ .spider .Z 2 1)

end SpLean.Algebraic.Gate
