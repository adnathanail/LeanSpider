import ZxLean

open ZxLean

def main : IO Unit :=
  IO.println "Open Main.lean in VS Code to see the ZX diagram in the InfoView."

def zHadHad : ZXDiagram :=
  ZXDiagram.ofList
    [.input 0, .spider .Z ⟨1, 1⟩, .hadamard, .hadamard, .output 0]
    [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩]
def zHadHadSimplified : ZXDiagram :=
  { nodes := [some (.input 0), some (.spider .Z ⟨1, 1⟩), none, none, some (.output 0)]
    edges := [⟨0, 1⟩, ⟨1, 4⟩] }
#html zHadHad.toHtml
#html zHadHadSimplified.toHtml

theorem dozHadHadSimp : zHadHad ≈z zHadHadSimplified := by
  zx_show
  zx_hadamard_hadamard 2 3
  zx_rfl
#print axioms dozHadHadSimp

#html zCnotZ.toHtml
#html cnot.toHtml
-- Z commutes with CNOT, and cancels with the second Z
theorem dozCnotZ : zCnotZ ≈z cnot := by
  zx_show
  zx_spider_fusion 1 2
  zx_spider_fusion 1 3
  zx_rfl
#print axioms dozCnotZ

def piPiPiMinus : ZXDiagram :=
  ZXDiagram.ofList
    [.input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨1, 1⟩, .spider .Z ⟨-1, 1⟩, .output 0]
    [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩]
def pppmSimplified : ZXDiagram :=
  { nodes := [some (.input 0), some (.spider .Z ⟨1, 1⟩), none, none, some (.output 0)]
    edges := [⟨0, 1⟩, ⟨1, 4⟩] }
#html piPiPiMinus.toHtml
#html pppmSimplified.toHtml

-- 3π ≣ π
theorem doPppmSimp : piPiPiMinus ≈z pppmSimplified := by
  zx_show
  -- Using Lean machinery to help us
  repeat zx_spider_fusion 1
  zx_rfl
#print axioms doPppmSimp

def piPiMinus : ZXDiagram :=
  ZXDiagram.ofList
    [.input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨1, 1⟩, .output 0]
    [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]
def ppmSimplified : ZXDiagram :=
  { nodes := [some (.input 0), none, none, some (.output 0)]
    edges := [⟨0, 3⟩] }
#html piPiMinus.toHtml
#html ppmSimplified.toHtml

theorem doPpmSimp : piPiMinus ≈z ppmSimplified := by
  zx_show
  -- Using a derived rule
  zx_pipi 1
  zx_rfl
-- But it still only depends on one of our 7 axiom rules
#print axioms doPpmSimp
