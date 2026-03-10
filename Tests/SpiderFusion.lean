import LSpec
import ZxLean

open LSpec

-- Test merging two spiders
def twoSpiders : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 2⟩, .spider .Z ⟨1, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]
def twoSpidersMerged : ZXDiagram :=
  { nodes := [some (.input 0), some (.spider .Z ⟨3, 2⟩), none, some (.output 0)]
    edges := [⟨0, 1⟩, ⟨1, 3⟩] }

-- Test merging three spiders
def threeSpiders : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 2⟩, .spider .Z ⟨1, 1⟩, .spider .Z ⟨3, 4⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩]
def threeSpidersMerged1 : ZXDiagram :=
  { nodes := [some (.input 0), some (.spider .Z ⟨3, 2⟩), none, some (.spider .Z ⟨3, 4⟩), some (.output 0)]
    edges := [⟨0, 1⟩, ⟨1, 3⟩, ⟨3, 4⟩] }
def threeSpidersMerged2 : ZXDiagram :=
  { nodes := [some (.input 0), some (.spider .Z ⟨9, 4⟩), none, none, some (.output 0)]
    edges := [⟨0, 1⟩, ⟨1, 4⟩] }

-- Spider fusing Z CNOT Z
def zCnotZ : ZXDiagram :=
  .ofList [
      .input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨0, 1⟩, .spider .Z ⟨1, 1⟩, .output 0,
      .input 1, .spider .X ⟨0, 1⟩, .output 1
    ]
    [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩, ⟨2, 6⟩, ⟨5, 6⟩, ⟨6, 7⟩]
def cnot : ZXDiagram :=
  { nodes := [some (.input 0), some (.spider .Z ⟨2, 1⟩), none, none, some (.output 0), some (.input 1), some (.spider .X ⟨0, 1⟩), some (.output 1)]
    edges := [⟨0, 1⟩, ⟨1, 4⟩, ⟨1, 6⟩, ⟨5, 6⟩, ⟨6, 7⟩] }

def spiderFusionTests : TestSeq :=
  test "merging two spiders" ((twoSpiders.spiderFusion 1 2).get! == twoSpidersMerged) $
  test "merging three spiders once" ((threeSpiders.spiderFusion 1 2).get! == threeSpidersMerged1) $
  test "merging three spiders twice" (((threeSpiders.spiderFusion 1 2).get!.spiderFusion 1 3).get! == threeSpidersMerged2) $
  test "simplifying Z CNOT Z to just CNOT" ((((zCnotZ.spiderFusion 1 2).get!).spiderFusion 1 3).get! == cnot)

#lspec spiderFusionTests
