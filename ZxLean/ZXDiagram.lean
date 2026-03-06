import Std.Data.HashMap

inductive SpiderColor where
  | Z  -- green
  | X  -- red
  deriving Repr, BEq

/-- Phase as a rational multiple of π, stored as p/q.
    e.g. phase 1 2 represents π/2 -/
structure Phase where
  num : Int
  den : Nat := 1
  deriving Repr, BEq

/-- a/b + c/d = (ad + bc)/bd -/
def Phase.add (p q : Phase) : Phase :=
  { num := p.num * q.den + q.num * p.den
    den := p.den * q.den }

instance : Add Phase where
  add := Phase.add

/-- Internal spider (Z/X) or input or output -/
inductive Node where
  | spider (color : SpiderColor) (phase : Phase)
  | input  (id : Nat)
  | output (id : Nat)
  deriving Repr, BEq

/-- Get the color of a node, if it is a spider -/
def Node.color? : Node → Option SpiderColor
  | .spider c _ => some c
  | _ => none

/-- Get the phase of a node, if it is a spider -/
def Node.phase? : Node → Option Phase
  | .spider _ p => some p
  | _ => none

/-- Stable node identifier -/
abbrev NodeId := Nat

/-- Edge between nodes identified by stable NodeId -/
structure Edge where
  src : NodeId
  tgt : NodeId
  deriving Repr, BEq

structure ZXDiagram where
  nodes  : Std.HashMap NodeId Node
  edges  : Array Edge
  nextId : NodeId := 0

/-- Build a ZXDiagram from arrays (array indices become node IDs) -/
def ZXDiagram.ofArrays (nodes : Array Node) (edges : Array Edge) : ZXDiagram :=
  let m := nodes.foldl (init := (Std.HashMap.emptyWithCapacity nodes.size, 0))
    fun (map, idx) n => (map.insert idx n, idx + 1)
  { nodes  := m.1
    edges  := edges
    nextId := nodes.size }

/-- Look up a node by its stable ID -/
def ZXDiagram.getNode? (d : ZXDiagram) (id : NodeId) : Option Node :=
  d.nodes[id]?

/-- Add a node, returning the updated diagram and the new node's ID -/
def ZXDiagram.addNode (d : ZXDiagram) (n : Node) : ZXDiagram × NodeId :=
  ({ d with nodes := d.nodes.insert d.nextId n, nextId := d.nextId + 1 }, d.nextId)

/-- Add an edge between two nodes -/
def ZXDiagram.addEdge (d : ZXDiagram) (e : Edge) : ZXDiagram :=
  { d with edges := d.edges.push e }

/-- Check whether two node IDs are connected by an edge -/
def ZXDiagram.connected (d : ZXDiagram) (a b : NodeId) : Bool :=
  d.edges.any fun e => (e.src == a && e.tgt == b) || (e.src == b && e.tgt == a)

/-- Get all neighbor IDs of a given node -/
def ZXDiagram.neighbors (d : ZXDiagram) (n : NodeId) : Array NodeId :=
  d.edges.foldl (init := #[]) fun acc e =>
    if e.src == n then acc.push e.tgt
    else if e.tgt == n then acc.push e.src
    else acc

/-- Remove all edges touching a given node ID -/
def ZXDiagram.removeEdgesOf (d : ZXDiagram) (n : NodeId) : ZXDiagram :=
  { d with edges := d.edges.filter fun e => e.src != n && e.tgt != n }

/-- Remove a node (no reindexing needed with stable IDs) -/
def ZXDiagram.removeNode (d : ZXDiagram) (n : NodeId) : ZXDiagram :=
  { d with nodes := d.nodes.erase n }

instance : Repr ZXDiagram where
  reprPrec d _ :=
    let nodesList := d.nodes.toList.mergeSort (fun a b => a.1 < b.1)
    let nodesRepr := nodesList.map fun (id, n) => repr id ++ " => " ++ repr n
    let edgesRepr := d.edges.toList.map repr
    "ZXDiagram { nodes := [" ++ Std.Format.joinSep nodesRepr ", " ++
    "], edges := [" ++ Std.Format.joinSep edgesRepr ", " ++
    "], nextId := " ++ repr d.nextId ++ " }"

-- instance : BEq ZXDiagram where
--   beq a b :=
--     let aSorted := a.nodes.toList.mergeSort (fun x y => x.1 < y.1)
--     let bSorted := b.nodes.toList.mergeSort (fun x y => x.1 < y.1)
--     aSorted == bSorted && a.edges == b.edges
