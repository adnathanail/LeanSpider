import LeanZX.Axioms
import LeanZX.Tactics

open Lean Elab Tactic Meta

def ZXDiagram.piCopy (d: ZXDiagram) (a b : NodeId) : Except String ZXDiagram := do
  -- Get node info
  let nodeA ← (d.getNode? a).toExcept s!"Node {a} not found"
  let nodeB ← (d.getNode? b).toExcept s!"Node {b} not found"
  let colorA ← (Node.color? nodeA).toExcept s!"Node {a} is not a spider"
  let colorB ← (Node.color? nodeB).toExcept s!"Node {b} is not a spider"
  let phaseA ← (Node.phase? nodeA).toExcept s!"Node {a} has no phase"
  let phaseB ← (Node.phase? nodeB).toExcept s!"Node {b} has no phase"
  -- Guards
  unless d.connected a b do throw s!"Nodes {a} and {b} are not connected"
  unless colorA ≠ colorB do throw s!"Nodes {a} and {b} must be different colours"
  unless phaseA == ⟨1, 1⟩ do throw s!"Node {a} must have a phase of π"
  let aNeighbors := d.neighbors a
  unless aNeighbors.length == 2 do throw s!"Node {a} must have one neighbour other than node {b}"

  let c ← (aNeighbors.filter (· != b))[0]?.toExcept s!"Node {a} has no neighbor other than {b}"
  let bOtherNeighbors := (d.neighbors b).filter (· != a)
  -- Remove A, negate B's phase, rewire
  let d := d.removeEdgesOf a
  let d := d.removeNode a
  let d := d.setNode b (Node.spider colorB ⟨-phaseB.num, phaseB.den⟩)
  let d := d.removeEdgesOf b
  let d := d.addEdge (Edge.mk c b)
  -- Add pi spiders on each of B's other legs
  let (d, piIds) := d.addNodes (bOtherNeighbors.map (λ _ => Node.spider colorA ⟨1, 1⟩))
  let d := d.addEdges (piIds.map (λ pi => Edge.mk b pi))
  let d := d.addEdges (bOtherNeighbors.zipWith (Edge.mk · ·) piIds)
  return d.normalize

namespace LeanZX

axiom ZXDiagram.piCopy_sound (d : ZXDiagram) (a b : NodeId) (d' : ZXDiagram) :
  d.piCopy a b = .ok d' → d ≈z d'

/-- Push an arity-2 pi spider through an adjacent spider of the opposite colour, inverting the second spider's phase. Shows the resulting diagram. -/
syntax "zx_pi" num num : tactic

elab_rules : tactic
  | `(tactic| zx_pi $a $b) =>
    applyRewrite a "Pi Copy"
      ``ZXDiagram.piCopy ``ZXDiagram.piCopy_sound
      #[mkNatLit a.getNat, mkNatLit b.getNat]

end LeanZX
