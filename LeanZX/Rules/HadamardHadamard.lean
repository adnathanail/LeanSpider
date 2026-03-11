import LeanZX.Axioms
import LeanZX.Tactics

open Lean Elab Tactic Meta

def ZXDiagram.hadamardHadamard (d: ZXDiagram) (a b : NodeId) : Except String ZXDiagram := do
  let nodeA ← (d.getNode? a).toExcept s!"Node {a} not found"
  let nodeB ← (d.getNode? b).toExcept s!"Node {b} not found"
  unless nodeA.isHadamard do throw s!"Node {a} is not a Hadamard"
  unless nodeB.isHadamard do throw s!"Node {b} is not a Hadamard"
  unless d.connected a b do throw s!"Nodes {a} and {b} are not connected"
  let aNeighbors := d.neighbors a |>.filter (· != b)
  let bNeighbors := d.neighbors b |>.filter (· != a)
  unless aNeighbors.length == 1 do throw s!"Node {a} has {aNeighbors.length} neighbours other than node {b} (should be 1)"
  unless bNeighbors.length == 1 do throw s!"Node {b} has {bNeighbors.length} neighbours other than node {a} (should be 1)"
  let n0 ← (aNeighbors[0]?).toExcept s!"Node {a} neighbour not found"
  let n1 ← (bNeighbors[0]?).toExcept s!"Node {b} neighbour not found"
  let d := d.removeEdgesOf a
  let d := d.removeNode a
  let d := d.removeEdgesOf b
  let d := d.removeNode b
  let d := { d with edges := d.edges ++ [Edge.mk n0 n1] }
  return d.normalize

namespace LeanZX

axiom ZXDiagram.hadamardHadamard_sound (d : ZXDiagram) (a b : NodeId) (d' : ZXDiagram) :
  d.hadamardHadamard a b = .ok d' → d ≈z d'

/-- Remove two connected degree-2 Hadamards. Shows the resulting diagram. -/
syntax "zx_hh" num num : tactic

elab_rules : tactic
  | `(tactic| zx_hh $a $b) =>
    applyRewrite a "Hadamard Hadamard"
      ``ZXDiagram.hadamardHadamard ``ZXDiagram.hadamardHadamard_sound
      #[mkNatLit a.getNat, mkNatLit b.getNat]

end LeanZX
