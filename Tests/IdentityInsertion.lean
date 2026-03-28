import LSpec
import LeanSpider.All

open LSpec LeanSpider

-- Simple wire: input—output
private def simpleWire : ZXDiagram :=
  .ofList [.input 0, .output 0]
          [⟨0, 1⟩]
private def simpleWireZInserted : ZXDiagram :=
  { nodes := [some (.input 0), some (.output 0), some (.spider .Z ⟨0, 1⟩)]
    edges := [⟨0, 2⟩, ⟨1, 2⟩] }
private def simpleWireXInserted : ZXDiagram :=
  { nodes := [some (.input 0), some (.output 0), some (.spider .X ⟨0, 1⟩)]
    edges := [⟨0, 2⟩, ⟨1, 2⟩] }

-- Two spiders connected
private def twoSpiders : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 2⟩, .spider .Z ⟨1, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]
private def twoSpidersZInserted : ZXDiagram :=
  { nodes := [some (.input 0), some (.spider .Z ⟨1, 2⟩), some (.spider .Z ⟨1, 1⟩), some (.output 0), some (.spider .Z ⟨0, 1⟩)]
    edges := [⟨0, 1⟩, ⟨1, 4⟩, ⟨2, 4⟩, ⟨2, 3⟩] }

-- Disconnected nodes (no edge between them)
private def disconnected : ZXDiagram :=
  .ofList [.input 0, .output 0]
          []

def identityInsertionTests : TestSeq :=
  test "insert Z spider on wire" ((simpleWire.identityInsertion 0 1 .Z).get! ≈z simpleWireZInserted) $
  test "insert X spider on wire" ((simpleWire.identityInsertion 0 1 .X).get! ≈z simpleWireXInserted) $
  test "insert between two spiders" ((twoSpiders.identityInsertion 1 2 .Z).get! ≈z twoSpidersZInserted) $
  test "disconnected nodes rejected" ((disconnected.identityInsertion 0 1 .Z).isError) $
  test "missing node rejected" ((simpleWire.identityInsertion 0 99 .Z).isError)

#lspec identityInsertionTests
