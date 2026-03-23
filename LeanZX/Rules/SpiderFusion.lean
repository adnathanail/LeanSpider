import LeanZX.Axioms
import LeanZX.Tactics

open Lean Elab Tactic Meta

def ZXDiagram.spiderFusion (d : ZXDiagram) (a b : NodeId) : Except String ZXDiagram := do
  -- Get node info
  let nodeA ← (d.getNode? a).toExcept s!"Node {a} not found"
  let nodeB ← (d.getNode? b).toExcept s!"Node {b} not found"
  let colorA ← (Node.color? nodeA).toExcept s!"Node {a} is not a spider"
  let colorB ← (Node.color? nodeB).toExcept s!"Node {b} is not a spider"
  let phaseA ← (Node.phase? nodeA).toExcept s!"Node {a} has no phase"
  let phaseB ← (Node.phase? nodeB).toExcept s!"Node {b} has no phase"
  -- Check we have two connected spiders of the same colours
  unless colorA == colorB do throw s!"Colors don't match: nodes {a} and {b}"
  unless d.connected a b do throw s!"Nodes {a} and {b} are not connected"
  -- New merged spider
  let merged := Node.spider colorA (phaseA + phaseB)
  -- Rewire edges from b's neighbors (except a) to now point to a
  let bNeighbors := d.neighbors b |>.filter (· != a)
  let newEdges := bNeighbors.map fun n => Edge.mk a n
  -- Remove all edges touching b, update node at a, then remove node b
  let d := d.removeEdgesOf b
  let d := d.setNode a merged
  let d := { d with edges := d.edges ++ newEdges }
  let d := d.removeNode b
  return d

namespace LeanZX

axiom ZXDiagram.spiderFusion_sound (d : ZXDiagram) (a b : NodeId) (d' : ZXDiagram) :
  d.spiderFusion a b = .ok d' → d ≈z d'

/-- Find the first neighbor of node `a` that can be fused with it (same-color spider). -/
private def findFusionPartner (d : ZXDiagram) (a : NodeId) : Option NodeId := do
  let nodeA ← d.getNode? a
  let colorA ← nodeA.color?
  (d.neighbors a).find? fun b =>
    match d.getNode? b with
    | some nodeB => match nodeB.color? with
      | some colorB => colorA == colorB
      | none => false
    | none => false

/-- Fuse two connected spiders of the same color. Shows the resulting diagram.
    With one argument, auto-finds a partner. Use `repeat zx_sp n` to fuse all. -/
syntax "zx_sp" num num : tactic
syntax "zx_sp" num : tactic

elab_rules : tactic
  | `(tactic| zx_sp $a $b) =>
    applyRewrite a "Spider fusion"
      ``ZXDiagram.spiderFusion ``ZXDiagram.spiderFusion_sound
      #[mkNatLit a.getNat, mkNatLit b.getNat]
  | `(tactic| zx_sp $a) => withMainContext do
    let goal ← getMainGoal
    let goalType ← goal.getType
    let (lhs, _) ← parseEquivGoal goalType
    let d ← evalZXDiagram lhs
    let some b := findFusionPartner d a.getNat
      | throwError "No fusable neighbor found for node {a.getNat}"
    applyRewrite a "Spider fusion"
      ``ZXDiagram.spiderFusion ``ZXDiagram.spiderFusion_sound
      #[mkNatLit a.getNat, mkNatLit b]

end LeanZX
