import LSpec
import LeanSpider.All

open LSpec LeanSpider

-- Basic: two opposite-color phase-0 spiders in a chain
--   in → Z(0) → X(0) → out
-- becomes: in → X(0) → Z(0) → out
private def basicChain : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨0, 1⟩, .spider .X ⟨0, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]
private def basicChainResult : ZXDiagram :=
  { nodes := [some (.input 0), none, none, some (.output 0),
              some (.spider .X ⟨0, 1⟩), some (.spider .Z ⟨0, 1⟩)]
    edges := [⟨0, 4⟩, ⟨3, 5⟩, ⟨4, 5⟩] }
-- #html basicChain.toHtml
-- #html basicChainResult.toHtml

-- Larger case: Z(0) with 3 neighbors, X(0) with 3 neighbors → complete bipartite K_{3,3}
private def threeByThree : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨0, 1⟩, .spider .X ⟨0, 1⟩, .output 0,
           .input 1, .output 1, .input 2, .output 2]
          [⟨0, 1⟩, ⟨4, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨2, 5⟩, ⟨1, 6⟩, ⟨2, 7⟩]
private def threeByThreeResult : ZXDiagram :=
  { nodes := [some (.input 0), none, none, some (.output 0),
              some (.input 1), some (.output 1), some (.input 2), some (.output 2),
              some (.spider .X ⟨0, 1⟩), some (.spider .X ⟨0, 1⟩), some (.spider .X ⟨0, 1⟩),
              some (.spider .Z ⟨0, 1⟩), some (.spider .Z ⟨0, 1⟩), some (.spider .Z ⟨0, 1⟩)]
    edges := [⟨0, 8⟩, ⟨3, 11⟩, ⟨4, 9⟩, ⟨5, 12⟩, ⟨6, 10⟩, ⟨7, 13⟩,
              ⟨8, 11⟩, ⟨8, 12⟩, ⟨8, 13⟩,
              ⟨9, 11⟩, ⟨9, 12⟩, ⟨9, 13⟩,
              ⟨10, 11⟩, ⟨10, 12⟩, ⟨10, 13⟩] }
-- #html threeByThree.toHtml
-- #html threeByThreeResult.toHtml

-- Error: same colour spiders
private def sameColour : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨0, 1⟩, .spider .Z ⟨0, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]
-- #html sameColour.toHtml

-- Error: non-zero phase
private def nonZeroPhase : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 2⟩, .spider .X ⟨0, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]
-- #html nonZeroPhase.toHtml

-- Error: not connected
private def notConnected : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨0, 1⟩, .spider .X ⟨0, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨2, 3⟩]
-- #html notConnected.toHtml

-- Error: non-spider node
private def nonSpider : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨0, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩]
-- #html nonSpider.toHtml

def strongCompTests : TestSeq :=
  test "basic chain" ((basicChain.strongComp 1 2).get! ≈z basicChainResult) $
  test "3x3 bipartite" ((threeByThree.strongComp 1 2).get! ≈z threeByThreeResult) $
  test "same colour rejected" ((sameColour.strongComp 1 2).isError) $
  test "non-zero phase rejected" ((nonZeroPhase.strongComp 1 2).isError) $
  test "not connected rejected" ((notConnected.strongComp 1 2).isError) $
  test "non-spider node rejected" ((nonSpider.strongComp 1 2).isError)

#lspec strongCompTests
