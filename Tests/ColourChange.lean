import LSpec
import LeanZX.All

open LSpec LeanZX

-- Colour change a Z spider to X, surrounded by Hadamards
private def zSpider : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 2⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩]
private def zSpiderColourChanged : ZXDiagram :=
  .ofList [.input 0, .spider .X ⟨1, 2⟩, .output 0, .hadamard, .hadamard]
          [⟨0, 3⟩, ⟨1, 3⟩, ⟨1, 4⟩, ⟨2, 4⟩]

-- Colour change an X spider to Z
private def xSpider : ZXDiagram :=
  .ofList [.input 0, .spider .X ⟨1, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩]
private def xSpiderColourChanged : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 1⟩, .output 0, .hadamard, .hadamard]
          [⟨0, 3⟩, ⟨1, 3⟩, ⟨1, 4⟩, ⟨2, 4⟩]

-- Error: not a spider
private def hadamardNode : ZXDiagram :=
  .ofList [.input 0, .hadamard, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩]

def colourChangeTests : TestSeq :=
  test "Z to X colour change" ((zSpider.colourChange 1).get! ≈z zSpiderColourChanged) $
  test "X to Z colour change" ((xSpider.colourChange 1).get! ≈z xSpiderColourChanged) $
  test "non-spider rejected" ((hadamardNode.colourChange 1).isError)

#lspec colourChangeTests
