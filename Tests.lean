import LSpec
import ZxLean

section LSpec

open LSpec

-- Test merging two spiders
def twoSpiders : ZXDiagram :=
  .ofArrays #[.input 0, .spider .Z ⟨1, 2⟩, .spider .Z ⟨1, 1⟩, .output 0]
            #[⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]
-- #html twoSpiders.toHtml
def twoSpidersMerged : ZXDiagram :=
  { nodes := #[some (.input 0), some (.spider .Z ⟨3, 2⟩), none, some (.output 0)]
    edges := #[⟨0, 1⟩, ⟨1, 3⟩] }
-- #html twoSpidersMerged.toHtml

#lspec test "merging two spiders" ((twoSpiders.spiderFusion 1 2).get! == twoSpidersMerged)

-- Test merging three spiders
def threeSpiders : ZXDiagram :=
  .ofArrays #[.input 0, .spider .Z ⟨1, 2⟩, .spider .Z ⟨1, 1⟩, .spider .Z ⟨3, 4⟩, .output 0]
            #[⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩]
-- #html threeSpiders.toHtml
def threeSpidersMerged1 : ZXDiagram :=
  { nodes := #[some (.input 0), some (.spider .Z ⟨3, 2⟩), none, some (.spider .Z ⟨3, 4⟩), some (.output 0)]
  -- TODO order edges normally
    edges := #[⟨0, 1⟩, ⟨3, 4⟩, ⟨1, 3⟩] }
-- #html threeSpidersMerged1.toHtml
def threeSpidersMerged2 : ZXDiagram :=  -- TODO simplify phase
  { nodes := #[some (.input 0), some (.spider .Z ⟨18, 8⟩), none, none, some (.output 0)]
    edges := #[⟨0, 1⟩, ⟨1, 4⟩] }
-- #html threeSpidersMerged2.toHtml

-- #html (threeSpiders.spiderFusion 1 2).get!.toHtml
-- #html ((threeSpiders.spiderFusion 1 2).get!.spiderFusion 1 3).get!.toHtml
-- TODO store intermediate result
#lspec test "merging three spiders once" ((threeSpiders.spiderFusion 1 2).get! == threeSpidersMerged1) $
       test "merging three spiders twice" (((threeSpiders.spiderFusion 1 2).get!.spiderFusion 1 3).get! == threeSpidersMerged2)

-- Spider fusing Z CNOT Z
def zCnotZ : ZXDiagram :=
  .ofArrays #[
      .input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨0, 1⟩, .spider .Z ⟨1, 1⟩, .output 0,
      .input 1, .spider .X ⟨0, 1⟩, .output 1
    ]
    #[⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩, ⟨2, 6⟩, ⟨5, 6⟩, ⟨6, 7⟩]
#html zCnotZ.toHtml
def cnot : ZXDiagram :=
  { nodes := #[some (.input 0), some (.spider .Z ⟨2, 1⟩), none, none, some (.output 0), some (.input 1), some (.spider .X ⟨0, 1⟩), some (.output 1)]
    edges := #[⟨0, 1⟩, ⟨5, 6⟩, ⟨6, 7⟩, ⟨1, 6⟩, ⟨1, 4⟩] }
#html cnot.toHtml
#lspec test "simplifying Z CNOT Z to just CNOT" ((((zCnotZ.spiderFusion 1 2).get!).spiderFusion 1 3).get! == cnot)

-- Identity removal (Z spider)
def justPhaseFreeZSpider : ZXDiagram :=
  .ofArrays #[.input 0, .spider .Z ⟨0, 1⟩, .output 0]
            #[⟨0, 1⟩, ⟨1, 2⟩]
def justPhaseFreeZSpiderIdentityRemoved : ZXDiagram :=
  { nodes := #[some (.input 0), none, some (.output 0)]
    edges := #[⟨0, 2⟩] }

#lspec test "removing phase-free Z spider" ((justPhaseFreeZSpider.identityRemoval 1).get! == justPhaseFreeZSpiderIdentityRemoved)

-- Identity removal (X spider)
def justPhaseFreeXSpider : ZXDiagram :=
  .ofArrays #[.input 0, .spider .X ⟨0, 1⟩, .output 0]
            #[⟨0, 1⟩, ⟨1, 2⟩]
def justPhaseFreeXSpiderIdentityRemoved : ZXDiagram :=
  { nodes := #[some (.input 0), none, some (.output 0)]
    edges := #[⟨0, 2⟩] }

#lspec test "removing phase-free X spider" ((justPhaseFreeXSpider.identityRemoval 1).get! == justPhaseFreeXSpiderIdentityRemoved)

-- Identity removal error
def aZSpiderWithPhase : ZXDiagram :=
  .ofArrays #[.input 0, .spider .Z ⟨1, 1⟩, .output 0]
            #[⟨0, 1⟩, ⟨1, 2⟩]
-- TODO test panicking
-- #lspec test "trying to identity remove spider with phase should fail" ((aZSpiderWithPhase.identityRemoval 1).get! == justPhaseFreeXSpiderIdentityRemoved)

end LSpec
