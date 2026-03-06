import ZxLean

/-- in -→ Z(π) -→ Z(2π) -→ out -/
def twoSpiders : ZXDiagram :=
  .ofArrays #[.input 0, .spider .Z ⟨1, 2⟩, .spider .Z ⟨1, 1⟩, .output 0]
            #[⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]

def empty_graph : ZXDiagram :=
  .ofArrays #[.input 0, .output 0]
            #[⟨0, 1⟩]

#html empty_graph.toHtml
#html twoSpiders.toHtml
#html ((twoSpiders.spiderFusion 1 2).getD empty_graph).toHtml

def threeSpiders : ZXDiagram :=
  .ofArrays #[.input 0, .spider .Z ⟨1, 2⟩, .spider .Z ⟨1, 1⟩, .spider .Z ⟨3, 4⟩, .output 0]
            #[⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩]

#html threeSpiders.toHtml
#html ((threeSpiders.spiderFusion 2 3).getD empty_graph).toHtml

def zCnotZ : ZXDiagram :=
  .ofArrays #[
      .input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨0, 1⟩, .spider .Z ⟨1, 1⟩, .output 0,
      .input 1, .spider .X ⟨0, 1⟩, .output 1
    ]
    #[⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩, ⟨2, 6⟩, ⟨5, 6⟩, ⟨6, 7⟩]

def zCnotZFusedA := (zCnotZ.spiderFusion 1 2).getD empty_graph
-- With stable IDs, after fusing 1+2, node 3 stays as 3 (not reindexed to 2)
def zCnotZFusedB := (zCnotZFusedA.spiderFusion 1 3).getD empty_graph

#html zCnotZ.toHtml
#html zCnotZFusedA.toHtml
#html zCnotZFusedB.toHtml

def main : IO Unit :=
  IO.println "Open Main.lean in VS Code to see the ZX diagram in the InfoView."
