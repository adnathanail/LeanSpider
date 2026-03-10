import ZxLean

open ZxLean

def main : IO Unit :=
  IO.println "Open Main.lean in VS Code to see the ZX diagram in the InfoView."

def piPiPiMinus : ZXDiagram :=
  ZXDiagram.ofList
    [.input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨1, 1⟩, .spider .Z ⟨-1, 1⟩, .output 0]
    [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩]

def pppmSimplified : ZXDiagram :=
  { nodes := [some (.input 0), some (.spider .Z ⟨1, 1⟩), none, none, some (.output 0)]
    edges := [⟨0, 1⟩, ⟨1, 4⟩] }

theorem doPppmSimp : piPiPiMinus ≈z pppmSimplified := by
  zx_show
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

theorem doPpmSimp : piPiMinus ≈z ppmSimplified := by
  zx_show
  zx_spider_fusion 1
  zx_id_removal 1
  zx_rfl

#print axioms doPpmSimp
