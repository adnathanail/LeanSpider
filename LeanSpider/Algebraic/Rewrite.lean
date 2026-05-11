import LeanSpider.Algebraic.ZX
import LeanSpider.ZXDiagram

namespace LeanSpider.Algebraic

open LeanSpider

/-- Count of `ZXDiagram` nodes that `ZX n m` lowers to, excluding the
    boundary inputs/outputs added at the top level. Mirrors `buildFrag`
    in `Visualize.lean` exactly so the IDs the tactic computes match
    those the user sees in the rendered diagram. -/
def ZX.nodeCount : {n m : Nat} → ZX n m → Nat
  | _, _, .empty    => 0
  | _, _, .wire     => 1
  | _, _, .hadamard => 1
  | _, _, .spider _ _ _ _ => 1
  | _, _, .stack   a b => a.nodeCount + b.nodeCount
  | _, _, .compose a b => a.nodeCount + b.nodeCount

/-- Attempt direct Z-spider fusion on a pair `(a, b)` that sit under a
    single `compose`. Succeeds only when `a` is a Z-spider with output
    arity 1 and `b` is a Z-spider with input arity 1; produces the fused
    spider `spider .Z n k (α + β)` with the raw phase sum. -/
def ZX.tryFuse {n mid k : Nat} (a : ZX n mid) (b : ZX mid k) :
    Option (ZX n k) :=
  match mid, a, b with
  | 1, .spider .Z _ 1 α, .spider .Z 1 _ β => some (.spider .Z _ _ (α + β))
  | _, _, _ => none

/-- Walker for `applySpiderFusionAt`. Threads an offset counter through
    the term in the same DFS order as `buildFrag` (so the IDs match the
    rendered diagram). At each `compose` whose two children have offsets
    `(idA, idB)`, attempts the direct fusion. -/
def ZX.applySpiderFusionAtAux : {n m : Nat} → ZX n m → NodeId → NodeId → Nat →
    Except String (ZX n m × Nat)
  | _, _, .empty, _, _, off => .ok (.empty, off)
  | _, _, .wire, _, _, off => .ok (.wire, off + 1)
  | _, _, .hadamard, _, _, off => .ok (.hadamard, off + 1)
  | _, _, .spider c i j φ, _, _, off => .ok (.spider c i j φ, off + 1)
  | _, _, .stack a b, idA, idB, off => do
      let (a', off1) ← ZX.applySpiderFusionAtAux a idA idB off
      let (b', off2) ← ZX.applySpiderFusionAtAux b idA idB off1
      .ok (.stack a' b', off2)
  | _, _, .compose a b, idA, idB, off =>
      let offA := off
      let offB := off + a.nodeCount
      let offEnd := offB + b.nodeCount
      if offA = idA ∧ offB = idB then
        match ZX.tryFuse a b with
        | some fused => .ok (fused, offEnd)
        | none =>
            .error
              s!"Nodes {idA} and {idB} are adjacent under a `compose`, \
                 but the pair is not a fuseable Z-spider junction \
                 (need Z-spider of arity (_, 1) followed by Z-spider \
                 of arity (1, _))."
      else do
        let (a', off1) ← ZX.applySpiderFusionAtAux a idA idB offA
        let (b', off2) ← ZX.applySpiderFusionAtAux b idA idB off1
        .ok (.compose a' b', off2)

/-- Top-level entry point: try to apply Z-spider fusion to the two
    spiders identified by `idA` (output spider) and `idB` (input spider).
    `idA`/`idB` are the IDs assigned by `ZX.toPositionedDiagram`. -/
def ZX.applySpiderFusionAt {n m : Nat} (z : ZX n m) (idA idB : NodeId) :
    Except String (ZX n m) := do
  let (z', _) ← ZX.applySpiderFusionAtAux z idA idB 0
  .ok z'

end LeanSpider.Algebraic
