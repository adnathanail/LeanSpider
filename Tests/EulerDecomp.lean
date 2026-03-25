import LSpec
import LeanZX.All

open LSpec LeanZX

def hadWire : ZXDiagram :=
  .ofList [.input 0, .hadamard, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩]

-- Expected results for each variant
def euExpected1 : ZXDiagram :=
  { nodes := [some (.input 0), none, some (.output 0),
              some (.spider .Z ⟨1, 2⟩), some (.spider .X ⟨1, 2⟩), some (.spider .Z ⟨1, 2⟩)]
    edges := [⟨0, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩, ⟨2, 5⟩] }

def euExpected2 : ZXDiagram :=
  { nodes := [some (.input 0), none, some (.output 0),
              some (.spider .Z ⟨-1, 2⟩), some (.spider .X ⟨-1, 2⟩), some (.spider .Z ⟨-1, 2⟩)]
    edges := [⟨0, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩, ⟨2, 5⟩] }

def euExpected3 : ZXDiagram :=
  { nodes := [some (.input 0), none, some (.output 0),
              some (.spider .Z ⟨1, 2⟩), some (.spider .X ⟨0, 1⟩),
              some (.spider .Z ⟨1, 2⟩), some (.spider .Z ⟨-1, 2⟩)]
    edges := [⟨0, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩, ⟨2, 5⟩, ⟨4, 6⟩] }

def euExpected4 : ZXDiagram :=
  { nodes := [some (.input 0), none, some (.output 0),
              some (.spider .X ⟨1, 2⟩), some (.spider .Z ⟨1, 2⟩), some (.spider .X ⟨1, 2⟩)]
    edges := [⟨0, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩, ⟨2, 5⟩] }

def euExpected5 : ZXDiagram :=
  { nodes := [some (.input 0), none, some (.output 0),
              some (.spider .X ⟨-1, 2⟩), some (.spider .Z ⟨-1, 2⟩), some (.spider .X ⟨-1, 2⟩)]
    edges := [⟨0, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩, ⟨2, 5⟩] }

def euExpected6 : ZXDiagram :=
  { nodes := [some (.input 0), none, some (.output 0),
              some (.spider .X ⟨1, 2⟩), some (.spider .Z ⟨0, 1⟩),
              some (.spider .X ⟨1, 2⟩), some (.spider .X ⟨-1, 2⟩)]
    edges := [⟨0, 3⟩, ⟨3, 4⟩, ⟨4, 5⟩, ⟨2, 5⟩, ⟨4, 6⟩] }

-- Error cases
def notHadamard : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨0, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩]

def branchedHadamard : ZXDiagram :=
  .ofList [.input 0, .hadamard, .output 0, .input 1]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 3⟩]

def eulerDecompTests : TestSeq :=
  test "variant 1: Z(π/2)-X(π/2)-Z(π/2)" ((hadWire.eulerDecomp 1 1).get! ≈z euExpected1) $
  test "variant 2: Z(-π/2)-X(-π/2)-Z(-π/2)" ((hadWire.eulerDecomp 1 2).get! ≈z euExpected2) $
  test "variant 3: Z(π/2)-X(0)-Z(π/2)+Z(-π/2)" ((hadWire.eulerDecomp 1 3).get! ≈z euExpected3) $
  test "variant 4: X(π/2)-Z(π/2)-X(π/2)" ((hadWire.eulerDecomp 1 4).get! ≈z euExpected4) $
  test "variant 5: X(-π/2)-Z(-π/2)-X(-π/2)" ((hadWire.eulerDecomp 1 5).get! ≈z euExpected5) $
  test "variant 6: X(π/2)-Z(0)-X(π/2)+X(-π/2)" ((hadWire.eulerDecomp 1 6).get! ≈z euExpected6) $
  test "non-Hadamard rejected" ((notHadamard.eulerDecomp 1 1).isError) $
  test "branched Hadamard rejected" ((branchedHadamard.eulerDecomp 1 1).isError) $
  test "invalid variant rejected" ((hadWire.eulerDecomp 1 7).isError) $
  test "node not found rejected" ((hadWire.eulerDecomp 99 1).isError)

#lspec eulerDecompTests
