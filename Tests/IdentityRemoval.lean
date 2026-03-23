import LSpec
import LeanZX.All

open LSpec LeanZX

-- Identity removal (Z spider)
def justPhaseFreeZSpider : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨0, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩]
def justPhaseFreeZSpiderIdentityRemoved : ZXDiagram :=
  { nodes := [some (.input 0), none, some (.output 0)]
    edges := [⟨0, 2⟩] }

-- Identity removal (X spider)
def justPhaseFreeXSpider : ZXDiagram :=
  .ofList [.input 0, .spider .X ⟨0, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩]
def justPhaseFreeXSpiderIdentityRemoved : ZXDiagram :=
  { nodes := [some (.input 0), none, some (.output 0)]
    edges := [⟨0, 2⟩] }

-- Identity removal should fail for spider with phase
def aZSpiderWithPhase : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩]

def identityRemovalTests : TestSeq :=
  test "removing phase-free Z spider" ((justPhaseFreeZSpider.identityRemoval 1).get! ≈z justPhaseFreeZSpiderIdentityRemoved) $
  test "removing phase-free X spider" ((justPhaseFreeXSpider.identityRemoval 1).get! ≈z justPhaseFreeXSpiderIdentityRemoved) $
  test "identity remove spider with phase should fail" ((aZSpiderWithPhase.identityRemoval 1).isError)

#lspec identityRemovalTests
