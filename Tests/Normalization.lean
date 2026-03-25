import LSpec
import LeanZX.All

open LSpec LeanZX

-- == Phase simplification tests ==

-- 2/2 simplifies to 1/1
private def unsimplifiedPhase : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨2, 2⟩, .output 0] [⟨0, 1⟩, ⟨1, 2⟩]
private def simplifiedPhase : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 1⟩, .output 0] [⟨0, 1⟩, ⟨1, 2⟩]

-- 6/4 simplifies to 3/2 then mod 2π stays 3/2 (since 3/2 < 2)
private def unsimplifiedPhase2 : ZXDiagram :=
  .ofList [.input 0, .spider .X ⟨6, 4⟩, .output 0] [⟨0, 1⟩, ⟨1, 2⟩]
private def simplifiedPhase2 : ZXDiagram :=
  .ofList [.input 0, .spider .X ⟨3, 2⟩, .output 0] [⟨0, 1⟩, ⟨1, 2⟩]

-- 2π (2/1) wraps to 0
private def phase2Pi : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨2, 1⟩, .output 0] [⟨0, 1⟩, ⟨1, 2⟩]
private def phase0 : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨0, 1⟩, .output 0] [⟨0, 1⟩, ⟨1, 2⟩]

-- 5π/2 wraps to π/2
private def phase5Over2 : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨5, 2⟩, .output 0] [⟨0, 1⟩, ⟨1, 2⟩]
private def phaseHalfPi : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 2⟩, .output 0] [⟨0, 1⟩, ⟨1, 2⟩]

-- 3π (3/1) wraps to π (1/1)
private def phase3Pi : ZXDiagram :=
  .ofList [.input 0, .spider .X ⟨3, 1⟩, .output 0] [⟨0, 1⟩, ⟨1, 2⟩]
private def phasePi : ZXDiagram :=
  .ofList [.input 0, .spider .X ⟨1, 1⟩, .output 0] [⟨0, 1⟩, ⟨1, 2⟩]

-- == Edge normalization tests (src ≤ tgt) ==

private def unsortedEdgeDir : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨0, 1⟩, .output 0] [⟨2, 1⟩, ⟨1, 0⟩]
private def sortedEdgeDir : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨0, 1⟩, .output 0] [⟨0, 1⟩, ⟨1, 2⟩]

-- == Edge sorting tests (edge list order) ==

private def unsortedEdgeOrder : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨0, 1⟩, .output 0] [⟨1, 2⟩, ⟨0, 1⟩]
private def sortedEdgeOrder : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨0, 1⟩, .output 0] [⟨0, 1⟩, ⟨1, 2⟩]

-- == Compaction tests ==

-- Compact removes nones and remaps edges
private def withNones : ZXDiagram :=
  { nodes := [some (.input 0), none, none, some (.output 0)]
    edges := [⟨0, 3⟩] }
private def withoutNones : ZXDiagram :=
  .ofList [.input 0, .output 0] [⟨0, 1⟩]

-- Compact with nones in the middle, multiple edges
private def sparseGraph : ZXDiagram :=
  { nodes := [some (.input 0), none, some (.spider .Z ⟨1, 2⟩), none, none, some (.output 0)]
    edges := [⟨0, 2⟩, ⟨2, 5⟩] }
private def sparseGraphCompacted : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 2⟩, .output 0] [⟨0, 1⟩, ⟨1, 2⟩]

-- Compact with no nones is identity
private def alreadyCompact : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 1⟩, .output 0] [⟨0, 1⟩, ⟨1, 2⟩]

-- Compact with trailing nones
private def trailingNones : ZXDiagram :=
  { nodes := [some (.input 0), some (.output 0), none, none, none]
    edges := [⟨0, 1⟩] }

-- == Combined: normalization + compaction ==

-- Diagram with nones, unsorted edges, and unsimplified phases
private def messy : ZXDiagram :=
  { nodes := [some (.input 0), none, some (.spider .Z ⟨4, 2⟩), none, some (.output 0)]
    edges := [⟨4, 2⟩, ⟨2, 0⟩] }
private def clean : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨0, 1⟩, .output 0] [⟨0, 1⟩, ⟨1, 2⟩]

def normalizationTests : TestSeq :=
  -- Compaction
  test "compact removes nones and remaps edges" (withNones ≈z withoutNones) $
  test "compact sparse graph" (sparseGraph ≈z sparseGraphCompacted) $
  test "compact is identity when no nones" (alreadyCompact ≈z alreadyCompact) $
  test "compact removes trailing nones" (trailingNones ≈z withoutNones) $
  -- Edge direction normalization
  test "edge direction normalized (src ≤ tgt)" (unsortedEdgeDir ≈z sortedEdgeDir) $
  -- Edge order normalization
  test "edge list sorted" (unsortedEdgeOrder ≈z sortedEdgeOrder) $
  -- Phase simplification
  test "phase 2/2 simplifies to 1/1" (unsimplifiedPhase ≈z simplifiedPhase) $
  test "phase 6/4 simplifies to 3/2" (unsimplifiedPhase2 ≈z simplifiedPhase2) $
  -- Phase mod 2π
  test "phase 2π wraps to 0" (phase2Pi ≈z phase0) $
  test "phase 5π/2 wraps to π/2" (phase5Over2 ≈z phaseHalfPi) $
  test "phase 3π wraps to π" (phase3Pi ≈z phasePi) $
  -- Combined
  test "compaction + normalization together" (messy ≈z clean)

#lspec normalizationTests
