import ZxLean.Axioms
import ZxLean.Tactics

open Lean Elab Tactic Meta

def ZXDiagram.identityRemoval (d: ZXDiagram) (a : NodeId) : Except String ZXDiagram := do
  -- Check the node being removed has no phase
  let node ← (d.getNode? a).toExcept s!"Node {a} not found"
  let phase ← (Node.phase? node).toExcept s!"Node {a} is not a spider"
  unless phase == ⟨0, 1⟩ do throw s!"Node {a} has non-zero phase"
  -- Check the node being removed only has 2 neighbors
  let neighbors := d.neighbors a
  unless neighbors.length == 2 do throw s!"Node {a} has {neighbors.length} neighbors, expected 2"
  -- Remove the node
  let n0 ← (neighbors[0]?).toExcept s!"Node {a} neighbor 0 not found"
  let n1 ← (neighbors[1]?).toExcept s!"Node {a} neighbor 1 not found"
  let d := d.removeEdgesOf a
  let d := d.removeNode a
  let d := { d with edges := d.edges ++ [Edge.mk n0 n1] }
  return d.normalize

namespace ZxLean

axiom ZXDiagram.identityRemoval_sound (d : ZXDiagram) (a : NodeId) (d' : ZXDiagram) :
  d.identityRemoval a = .ok d' → d ≈z d'

/-- Remove an identity (phase-0, degree-2) spider. Shows the resulting diagram. -/
syntax "zx_id" num : tactic

elab_rules : tactic
  | `(tactic| zx_id $a) =>
    applyRewrite a "Identity removal"
      ``ZXDiagram.identityRemoval ``ZXDiagram.identityRemoval_sound
      #[mkNatLit a.getNat]

end ZxLean
