import LeanZX.Axioms
import LeanZX.Tactics

open Lean Elab Tactic Meta

def ZXDiagram.colourChange (d: ZXDiagram) (a : NodeId) : Except String ZXDiagram := do
  -- Get node info
  let nodeA ← (d.getNode? a).toExcept s!"Node {a} not found"
  let colorA ← (Node.color? nodeA).toExcept s!"Node {a} is not a spider"
  let phaseA ← (Node.phase? nodeA).toExcept s!"Node {a} has no phase"
  let aNeighbors := d.neighbors a
  -- Flip node colour
  let newColour := if colorA == SpiderColor.X then SpiderColor.Z else SpiderColor.X
  let aColourChanged := Node.spider newColour phaseA
  let d := d.setNode a aColourChanged
  -- Add Hadamards
  let (d, hadIds) := d.addNodes (aNeighbors.map (λ _ => Node.hadamard))
  -- Rewire edges
  let d := d.removeEdgesOf a
  let d := d.addEdges (hadIds.map (λ had => Edge.mk had a))
  let d := d.addEdges (aNeighbors.zipWith (Edge.mk . .) hadIds)
  return d

namespace LeanZX

axiom ZXDiagram.colourChange_sound (d : ZXDiagram) (a : NodeId) (d' : ZXDiagram) :
  d.colourChange a = .ok d' → d ≈z d'

/-- Swap the colour of a Z or X spider, and surround it with Hadamards. Shows the resulting diagram. -/
syntax "zx_cc" num : tactic

elab_rules : tactic
  | `(tactic| zx_cc $a) =>
    applyRewrite a "Colour Change"
      ``ZXDiagram.colourChange ``ZXDiagram.colourChange_sound
      #[mkNatLit a.getNat]

end LeanZX
