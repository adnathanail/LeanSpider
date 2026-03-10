import ZxLean.ZXDiagram

/-- Canonicalize an edge so that src ≤ tgt (edges are undirected) -/
def Edge.normalize (e : Edge) : Edge :=
  if e.src ≤ e.tgt then e else { src := e.tgt, tgt := e.src }

/-- Normalize a diagram: canonicalize edge direction, sort edges, and simplify phases -/
def ZXDiagram.normalize (d : ZXDiagram) : ZXDiagram :=
  { nodes := d.nodes.map fun
      | some (.spider c p) => some (.spider c p.simplify)
      | n => n
    edges := (d.edges.map Edge.normalize).insertionSort }

def ZXDiagram.spiderFusion (d : ZXDiagram) (a b : NodeId) : Option ZXDiagram := do
  -- Get node info
  let nodeA ← d.getNode? a
  let nodeB ← d.getNode? b
  let colorA ← Node.color? nodeA
  let colorB ← Node.color? nodeB
  let phaseA ← Node.phase? nodeA
  let phaseB ← Node.phase? nodeB
  -- Check we have two connected spiders of the same colours
  guard (colorA == colorB)
  guard (d.connected a b)
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
  return d.normalize

def ZXDiagram.identityRemoval (d: ZXDiagram) (a : NodeId) : Option ZXDiagram := do
  -- Check the node being removed has no phase
  let node ← d.getNode? a
  let phase ← Node.phase? node
  guard (phase == ⟨0, 1⟩)
  -- Check the node being removed only has 2 neighbors
  let neighbors := d.neighbors a
  guard (neighbors.length == 2)
  -- Remove the node
  let n0 ← neighbors[0]?
  let n1 ← neighbors[1]?
  let d := d.removeEdgesOf a
  let d := d.removeNode a
  let d := { d with edges := d.edges ++ [Edge.mk n0 n1] }
  return d.normalize
