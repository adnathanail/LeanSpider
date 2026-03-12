import LeanZX

open LeanZX

def main : IO Unit :=
  IO.println "Open Main.lean in VS Code to see the ZX diagram in the InfoView."

def zHadX : ZXDiagram :=
  ZXDiagram.ofList
    [.input 0, .spider .Z ⟨1, 1⟩, .hadamard, .spider .X ⟨1, 1⟩, .output 0]
    [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩]
def zHadXSimplified : ZXDiagram :=
  { nodes := [some (.input 0), none, none, none, some (.output 0), none, some (.hadamard)]
    edges := [⟨0, 6⟩, ⟨4, 6⟩] }
#html zHadX.toHtml
#html zHadXSimplified.toHtml

theorem zHadXSimp : zHadX ≈z zHadXSimplified := by
  zx_show
  zx_cc 3
  zx_hh 2 5
  zx_sp 1 3
  zx_id 1
  zx_rfl
#print axioms zHadXSimp

#html zCnotZ.toHtml
#html cnot.toHtml
-- Z commutes with CNOT, and cancels with the second Z
theorem dozCnotZ : zCnotZ ≈z cnot := by
  zx_show
  zx_sp 1 2
  zx_sp 1 3
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
  repeat zx_sp 1
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

def exercise3point7 : ZXDiagram :=
  ZXDiagram.ofList
    [
      .input 0, .spider .X ⟨0, 1⟩, .spider .Z ⟨0, 1⟩, .output 0,
      .hadamard,
      .input 1, .spider .X ⟨0, 1⟩, .hadamard, .spider .Z ⟨0, 1⟩, .hadamard, .spider .Z ⟨0, 1⟩, .output 1,
      .spider .Z ⟨0, 1⟩, .spider .Z ⟨0, 1⟩, .spider .X ⟨1, 1⟩, .spider .X ⟨0, 1⟩,
    ]
    [
      ⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩,
      ⟨4, 3⟩,
      ⟨5, 6⟩, ⟨6, 7⟩, ⟨7, 8⟩, ⟨8, 9⟩, ⟨9, 10⟩, ⟨10, 11⟩,
      ⟨12, 13⟩, ⟨13, 6⟩, ⟨13, 14⟩, ⟨14, 15⟩,
    ]
#html exercise3point7.toHtml

-- Aimless exploration: just play with a diagram and see what happens
example : ∃ d', exercise3point7 ≈z d' := by
  zx_explore
  zx_sp 12 13
  zx_sp 14 15
  zx_id 12
  zx_sp 14 6
  zx_cc 8
  zx_hh 7 16
  zx_hh 9 17
  zx_sp 14 8
  zx_rfl
