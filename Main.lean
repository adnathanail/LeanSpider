import ZxLean

open ZxLean

def main : IO Unit :=
  IO.println "Open Main.lean in VS Code to see the ZX diagram in the InfoView."

-- Example: input — Z(π) — Z(-π) — output
-- Spider fusion merges into Z(0), then identity removal eliminates it.
def exampleDiagram : ZXDiagram :=
  ZXDiagram.ofArrays
    #[.input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨-1, 1⟩, .output 0]
    #[⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]

-- After fusing spiders 1 and 2
def afterFusion : ZXDiagram :=
  { nodes := #[some (.input 0), some (.spider .Z ⟨0, 1⟩), none, some (.output 0)]
    edges := #[⟨0, 1⟩, ⟨1, 3⟩] }

-- After removing the identity spider at node 1
def afterRemoval : ZXDiagram :=
  { nodes := #[some (.input 0), none, none, some (.output 0)]
    edges := #[⟨0, 3⟩] }

-- Prove the rewrite steps compute correctly
theorem fusion_step : exampleDiagram.spiderFusion 1 2 = some afterFusion := by native_decide
theorem removal_step : afterFusion.identityRemoval 1 = some afterRemoval := by native_decide

-- Chain both axioms to prove the full simplification preserves equivalence
theorem full_simplification : exampleDiagram ≈z afterRemoval :=
  ZXDiagram.equiv_trans
    (ZXDiagram.spiderFusion_sound exampleDiagram 1 2 afterFusion fusion_step)
    (ZXDiagram.identityRemoval_sound afterFusion 1 afterRemoval removal_step)

#print axioms full_simplification
