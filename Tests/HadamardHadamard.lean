import LSpec
import LeanZX.All

open LSpec LeanZX

-- Two adjacent Hadamards cancel
def twoHadamards : ZXDiagram :=
  .ofList [.input 0, .hadamard, .hadamard, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]
def twoHadamardsCancelled : ZXDiagram :=
  { nodes := [some (.input 0), none, none, some (.output 0)]
    edges := [⟨0, 3⟩] }

-- Error: nodes are not both Hadamards
def hadamardAndSpider : ZXDiagram :=
  .ofList [.input 0, .hadamard, .spider .Z ⟨0, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]

-- Error: nodes are not connected
def disconnectedHadamards : ZXDiagram :=
  .ofList [.input 0, .hadamard, .hadamard, .output 0]
          [⟨0, 1⟩, ⟨2, 3⟩]

-- Error: Hadamard has too many neighbours
def branchedHadamard : ZXDiagram :=
  .ofList [.input 0, .hadamard, .hadamard, .output 0, .input 1]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨4, 1⟩]

def hadamardHadamardTests : TestSeq :=
  test "two Hadamards cancel" ((twoHadamards.hadamardHadamard 1 2).get! ≈z twoHadamardsCancelled) $
  test "non-Hadamard rejected" ((hadamardAndSpider.hadamardHadamard 1 2).isError) $
  test "disconnected rejected" ((disconnectedHadamards.hadamardHadamard 1 2).isError) $
  test "branched Hadamard rejected" ((branchedHadamard.hadamardHadamard 1 2).isError)

#lspec hadamardHadamardTests
