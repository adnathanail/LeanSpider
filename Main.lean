import ZxLean

open ZxLean

def main : IO Unit :=
  IO.println "Open Main.lean in VS Code to see the ZX diagram in the InfoView."

-- Example: input — Z(π) — Z(-π) — output
-- Spider fusion merges into Z(0), then identity removal eliminates it.
def exampleDiagram : ZXDiagram :=
  ZXDiagram.ofList
    [.input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨-1, 1⟩, .output 0]
    [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]

-- The final simplified diagram: just input wired to output
def simplified : ZXDiagram :=
  { nodes := [some (.input 0), none, none, some (.output 0)]
    edges := [⟨0, 3⟩] }

-- Prove equivalence using tactics — each step shows the diagram in InfoView
theorem simplification : exampleDiagram ≈z simplified := by
  zx_show
  zx_spider_fusion 1 2
  zx_id_removal 1
  zx_rfl

#print axioms simplification
