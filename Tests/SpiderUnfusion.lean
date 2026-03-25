import LSpec
import LeanZX.All

open LSpec LeanZX

-- Fuse two Z(π/2) and Z(π) spiders, then unfuse back with the same phase split.
-- The round-trip changes node ordering (unfusion appends the new spider at the end),
-- so the result is ≈z to a diagram with nodes reordered: [input, Z(π/2), output, Z(π)].
private def twoSpiders : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 2⟩, .spider .Z ⟨1, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]
private def twoSpidersRoundTrip : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 2⟩, .output 0, .spider .Z ⟨1, 1⟩]
          [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 3⟩]

-- Fuse two X spiders with phases π/4 and 3π/4, then unfuse with a different split: π/2 and π/2.
private def twoXSpiders : ZXDiagram :=
  .ofList [.input 0, .spider .X ⟨1, 4⟩, .spider .X ⟨3, 4⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]
private def twoXSpidersDifferentSplit : ZXDiagram :=
  .ofList [.input 0, .spider .X ⟨1, 2⟩, .output 0, .spider .X ⟨1, 2⟩]
          [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 3⟩]

-- Fuse three Z spiders into one, then unfuse once to split off the last neighbor.
private def threeSpiders : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 2⟩, .spider .Z ⟨1, 1⟩, .spider .Z ⟨3, 4⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩]
-- After fusing all three into node 1 (phase 9/4), unfuse with α=1/2, β=7/4, rewire=[4]
private def threeSpidersPartialUnfuse : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨1, 2⟩, .output 0, .spider .Z ⟨7, 4⟩]
          [⟨0, 1⟩, ⟨1, 3⟩, ⟨2, 3⟩]

-- Unfusion→fusion round-trip: start with a single merged spider, unfuse then fuse back.
-- The new spider is appended at the end; fusion removes it, leaving a trailing none
-- that compact drops — so the result is structurally identical to the original.
private def singleZSpider : ZXDiagram :=
  .ofList [.input 0, .spider .Z ⟨3, 2⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩]

private def singleXSpider : ZXDiagram :=
  .ofList [.input 0, .spider .X ⟨1, 1⟩, .output 0]
          [⟨0, 1⟩, ⟨1, 2⟩]

-- Spider with three neighbors: unfuse to split off one, then fuse back.
private def branchedSpider : ZXDiagram :=
  .ofList [.input 0, .input 1, .spider .Z ⟨1, 1⟩, .output 0, .output 1]
          [⟨0, 2⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨2, 4⟩]

def spiderUnfusionTests : TestSeq :=
  -- Unfuse then fuse: exact round-trip back to original
  test "unfuse then fuse single Z spider"
    (let unfused := (singleZSpider.spiderUnfusion 1 ⟨1, 2⟩ ⟨1, 1⟩ [2]).get!
     let refused := (unfused.spiderFusion 1 3).get!
     refused ≈z singleZSpider) $
  test "unfuse then fuse single X spider"
    (let unfused := (singleXSpider.spiderUnfusion 1 ⟨1, 2⟩ ⟨1, 2⟩ [2]).get!
     let refused := (unfused.spiderFusion 1 3).get!
     refused ≈z singleXSpider) $
  test "unfuse then fuse branched spider"
    (let unfused := (branchedSpider.spiderUnfusion 2 ⟨1, 2⟩ ⟨1, 2⟩ [3, 4]).get!
     let refused := (unfused.spiderFusion 2 5).get!
     refused ≈z branchedSpider) $
  -- Fuse then unfuse (node ordering changes, compare against expected)
  test "fuse then unfuse two Z spiders"
    (let fused := (twoSpiders.spiderFusion 1 2).get!
     let unfused := (fused.spiderUnfusion 1 ⟨1, 2⟩ ⟨1, 1⟩ [3]).get!
     unfused ≈z twoSpidersRoundTrip) $
  -- Fuse then unfuse with a different phase split
  test "fuse then unfuse two X spiders with different split"
    (let fused := (twoXSpiders.spiderFusion 1 2).get!
     let unfused := (fused.spiderUnfusion 1 ⟨1, 2⟩ ⟨1, 2⟩ [3]).get!
     unfused ≈z twoXSpidersDifferentSplit) $
  -- Fuse three, then partially unfuse
  test "fuse three then unfuse once"
    (let fused1 := (threeSpiders.spiderFusion 1 2).get!
     let fused2 := (fused1.spiderFusion 1 3).get!
     let unfused := (fused2.spiderUnfusion 1 ⟨1, 2⟩ ⟨7, 4⟩ [4]).get!
     unfused ≈z threeSpidersPartialUnfuse) $
  -- Error: phases don't sum correctly
  test "unfusion fails when phases don't sum"
    (let fused := (twoSpiders.spiderFusion 1 2).get!
     (fused.spiderUnfusion 1 ⟨1, 2⟩ ⟨1, 2⟩ [3]).isError) $
  -- Error: rewire target not a neighbor
  test "unfusion fails when rewire target not a neighbor"
    (let fused := (twoSpiders.spiderFusion 1 2).get!
     (fused.spiderUnfusion 1 ⟨1, 2⟩ ⟨1, 1⟩ [2]).isError)

#lspec spiderUnfusionTests
