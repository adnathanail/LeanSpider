import ZxLean

open ProofWidgets

/-- in -→ Z(π) -→ Z(2π) -→ out -/
def twoSpiders : ZXDiagram :=
  { nodes := #[.input 0, .spider .Z ⟨1, 2⟩, .spider .Z ⟨1, 1⟩, .output 0]
    edges := #[⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩] }

/-- in -→ Z(3π) -→ out -/
-- def fused : ZXDiagram :=
--   { nodes := #[.input 0, .spider .Z ⟨3, 1⟩, .output 0]
--     edges := #[⟨0, 1⟩, ⟨1, 2⟩] }

def empty_graph : ZXDiagram :=
  { nodes := #[.input 0, .output 0]
    edges := #[⟨0, 1⟩] }

-- #eval twoSpiders.spiderFusion 1 2
-- #eval some fused
-- #eval twoSpiders.spiderFusion 1 2 == some fused

#html (Html.ofComponent ZXWidget ⟨empty_graph.toJson⟩ #[])
#html (Html.ofComponent ZXWidget ⟨twoSpiders.toJson⟩ #[])
#html (Html.ofComponent ZXWidget ⟨((twoSpiders.spiderFusion 1 2).getD empty_graph).toJson⟩ #[])

def main : IO Unit :=
  IO.println "Open Main.lean in VS Code to see the ZX diagram in the InfoView."
