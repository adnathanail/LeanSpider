import LSpec
import LeanZX.All

open LSpec LeanZX

-- Test merging two spiders
private def twoSpiders : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 2⟩, .spider .Z ⟨1, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]
private def twoSpidersMerged : ZXDiagram :=
  { nodes := [some (.input 0), some (.spider .Z ⟨3, 2⟩), none, some (.output 0)]
    edges := [⟨0, 1⟩, ⟨1, 3⟩] }

-- Test merging three spiders
private def threeSpiders : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 2⟩, .spider .Z ⟨1, 1⟩, .spider .Z ⟨3, 4⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩]
private def threeSpidersMerged1 : ZXDiagram :=
  { nodes := [some (.input 0), some (.spider .Z ⟨3, 2⟩), none, some (.spider .Z ⟨3, 4⟩), some (.output 0)]
    edges := [⟨0, 1⟩, ⟨1, 3⟩, ⟨3, 4⟩] }
private def threeSpidersMerged2 : ZXDiagram :=
  { nodes := [some (.input 0), some (.spider .Z ⟨9, 4⟩), none, none, some (.output 0)]
    edges := [⟨0, 1⟩, ⟨1, 4⟩] }

-- Test merging two π spiders gives identity (π + π = 2π ≡ 0 mod 2π)
private def twoPiSpiders : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨1, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]
private def twoPiSpidersMerged : ZXDiagram :=
  { nodes := [some (.input 0), some (.spider .Z ⟨0, 1⟩), none, some (.output 0)]
    edges := [⟨0, 1⟩, ⟨1, 3⟩] }

def spiderFusionTests : TestSeq :=
  test "merging two spiders" ((twoSpiders.spiderFusion 1 2).get! ≈z twoSpidersMerged) $
  test "merging three spiders once" ((threeSpiders.spiderFusion 1 2).get! ≈z threeSpidersMerged1) $
  test "merging three spiders twice" (((threeSpiders.spiderFusion 1 2).get!.spiderFusion 1 3).get! ≈z threeSpidersMerged2) $
  test "simplifying Z CNOT Z to just CNOT" ((((zCnotZ.spiderFusion 1 2).get!).spiderFusion 1 3).get! ≈z cnot) $
  test "two π spiders fuse to identity (phase 0)" ((twoPiSpiders.spiderFusion 1 2).get! ≈z twoPiSpidersMerged)

#lspec spiderFusionTests
