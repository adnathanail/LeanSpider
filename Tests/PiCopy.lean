import LSpec
import LeanZX.All

open LSpec LeanZX

-- Test pushing a green π spider through an adjacent red π/2 spider
private def piCopyBasic : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 1⟩, .spider .X ⟨1, 2⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]
private def piCopyBasicResult : ZXDiagram :=
  { nodes := [some (.input 0), none, some (.spider .X ⟨3, 2⟩), some (.output 0),
              some (.spider .Z ⟨1, 1⟩)]
    edges := [⟨0, 2⟩, ⟨2, 4⟩, ⟨3, 4⟩] }

-- Test error: same colour spiders
private def sameColour : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨1, 2⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]

-- Test error: non-π phase
private def nonPiPhase : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 2⟩, .spider .X ⟨1, 2⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]

-- Test error: π spider with too many neighbors
private def tooManyNeighbors : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 1⟩, .spider .X ⟨1, 2⟩, .output 0, .input 1]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨4, 1⟩]

def piCopyTests : TestSeq :=
  test "basic pi copy" ((piCopyBasic.piCopy 1 2).get! ≈z piCopyBasicResult) $
  test "same colour rejected" ((sameColour.piCopy 1 2).isError) $
  test "non-π phase rejected" ((nonPiPhase.piCopy 1 2).isError) $
  test "too many neighbors rejected" ((tooManyNeighbors.piCopy 1 2).isError)

#lspec piCopyTests
