import LeanSpider.Axioms
import LeanSpider.Tactics

open Lean Elab Tactic Meta

/-- Strong complementarity rule.
    Given two connected opposite-color phase-0 spiders Z and X,
      replace them with a complete bipartite graph:
        one new X-spider per Z-neighbor, one new Z-spider per X-neighbor,
        with every new X connected to every new Z. -/
def ZXDiagram.strongComp (d : ZXDiagram) (a b : NodeId) : Except String ZXDiagram := do
  -- Get node info
  let nodeA ← (d.getNode? a).toExcept s!"Node {a} not found"
  let nodeB ← (d.getNode? b).toExcept s!"Node {b} not found"
  let colorA ← (Node.color? nodeA).toExcept s!"Node {a} is not a spider"
  let colorB ← (Node.color? nodeB).toExcept s!"Node {b} is not a spider"
  let phaseA ← (Node.phase? nodeA).toExcept s!"Node {a} has no phase"
  let phaseB ← (Node.phase? nodeB).toExcept s!"Node {b} has no phase"
  -- Guards
  -- TODO check there is exactly 1 connection
  unless d.connected a b do throw s!"Nodes {a} and {b} are not connected"
  unless colorA ≠ colorB do throw s!"Nodes {a} and {b} must be different colours"
  unless phaseA == ⟨0, 1⟩ do throw s!"Node {a} must have phase 0"
  unless phaseB == ⟨0, 1⟩ do throw s!"Node {b} must have phase 0"
  -- Collect neighbors (excluding each other)
  let aNeighbors := (d.neighbors a).filter (· != b)
  let bNeighbors := (d.neighbors b).filter (· != a)
  -- Remove both spiders and their edges
  let d := d.removeEdgesOf a
  let d := d.removeEdgesOf b
  let d := d.removeNode a
  let d := d.removeNode b
  -- Create new spiders: one B-colored spider per A-neighbor, one A-colored spider per B-neighbor
  let (d, newBColorIds) := d.addNodes (aNeighbors.map (λ _ => Node.spider colorB ⟨0, 1⟩))
  let (d, newAColorIds) := d.addNodes (bNeighbors.map (λ _ => Node.spider colorA ⟨0, 1⟩))
  -- Connect each A-neighbor to its corresponding new B-colored spider
  let d := d.addEdges (aNeighbors.zipWith (Edge.mk · ·) newBColorIds)
  -- Connect each B-neighbor to its corresponding new A-colored spider
  let d := d.addEdges (bNeighbors.zipWith (Edge.mk · ·) newAColorIds)
  -- Connect every new B-colored spider to every new A-colored spider (complete bipartite)
  let bipartiteEdges := newBColorIds.foldl (init := []) fun acc xId =>
    acc ++ newAColorIds.map (Edge.mk xId ·)
  let d := d.addEdges bipartiteEdges
  return d.normalize

namespace LeanSpider

axiom ZXDiagram.strongComp_sound (d : ZXDiagram) (a b : NodeId) (d' : ZXDiagram) :
  d.strongComp a b = .ok d' → d ≈z d'

/-- Apply strong complementarity to two connected opposite-color phase-0 spiders.
    Shows the resulting diagram. -/
syntax "zx_sc" num num : tactic

elab_rules : tactic
  | `(tactic| zx_sc $a $b) =>
    applyRewrite a "Strong complementarity"
      ``ZXDiagram.strongComp ``ZXDiagram.strongComp_sound
      #[mkNatLit a.getNat, mkNatLit b.getNat]

end LeanSpider
