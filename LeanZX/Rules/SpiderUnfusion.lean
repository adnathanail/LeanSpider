import LeanZX.Axioms
import LeanZX.Tactics

open Lean Elab Tactic Meta Term

def ZXDiagram.spiderUnfusion (d : ZXDiagram) (a : NodeId) (α β : Phase)
    (rewire : List NodeId) : Except String ZXDiagram := do
  let nodeA ← (d.getNode? a).toExcept s!"Node {a} not found"
  let colorA ← (Node.color? nodeA).toExcept s!"Node {a} is not a spider"
  let phaseA ← (Node.phase? nodeA).toExcept s!"Node {a} has no phase"
  unless (α + β) == phaseA do
    throw s!"Phases {repr α} + {repr β} do not sum to node {a}'s phase {repr phaseA}"
  -- Check all rewire targets are neighbors of a
  let aNeighbors := d.neighbors a
  rewire.forM fun n =>
    unless aNeighbors.contains n do
      throw s!"Node {n} is not connected to node {a}"
  -- Move edges from a to rewire nodes over to the new spider b
  let d := { d with edges := d.edges.filter fun e =>
    !((e.src == a && rewire.contains e.tgt) || (e.tgt == a && rewire.contains e.src)) }
  -- Replace node a with phase α
  let d := d.setNode a (Node.spider colorA α)
  -- Add new same-color spider b with phase β
  let (d, b) := d.addNode (Node.spider colorA β)
  -- Connect a and b
  let d := d.addEdge (Edge.mk a b)
  -- Connect b to the rewired nodes
  let d := d.addEdges (rewire.map (Edge.mk b ·))
  return d.normalize

namespace LeanZX

axiom ZXDiagram.spiderUnfusion_sound (d : ZXDiagram) (a : NodeId) (α β : Phase)
    (rewire : List NodeId) (d' : ZXDiagram) :
  d.spiderUnfusion a α β rewire = .ok d' → d ≈z d'

/-- Split spider `a` into two connected spiders with phases `⟨αNum, αDen⟩` and `⟨βNum, βDen⟩`
    (as multiples of π, which must sum to the original phase). The nodes in `rewire` are
    detached from `a` and reattached to the new spider.
    Usage: `zx_unsp <nodeId> ⟨αNum, αDen⟩ ⟨βNum, βDen⟩ [n₁, n₂, ...]` -/
syntax "zx_unsp" num "⟨" num "," num "⟩" "⟨" num "," num "⟩" "[" (num),* "]" : tactic

elab_rules : tactic
  | `(tactic| zx_unsp $a ⟨$αn, $αd⟩ ⟨$βn, $βd⟩ [ $rewire,* ]) => do
    let mkPhase (n d : Nat) : MetaM Expr := do
      let numExpr ← mkAppM ``Int.ofNat #[mkNatLit n]
      mkAppM ``Phase.mk #[numExpr, mkNatLit d]
    let α ← mkPhase αn.getNat αd.getNat
    let β ← mkPhase βn.getNat βd.getNat
    let nilExpr ← mkAppOptM ``List.nil #[some (mkConst ``Nat)]
    let rewireList ← rewire.getElems.toList.foldrM
      (fun n acc => mkAppM ``List.cons #[mkNatLit n.getNat, acc])
      nilExpr
    applyRewrite a "Spider unfusion"
      ``ZXDiagram.spiderUnfusion ``ZXDiagram.spiderUnfusion_sound
      #[mkNatLit a.getNat, α, β, rewireList]

end LeanZX
