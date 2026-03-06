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
  nodes : Array (Option Node)
  edges : Array Edge
  deriving Repr, BEq

/-- Build a ZXDiagram from an array of nodes (array indices become node IDs) -/
def ZXDiagram.ofArrays (nodes : Array Node) (edges : Array Edge) : ZXDiagram :=
  { nodes := nodes.map some, edges := edges }

/-- Look up a node by its stable ID -/
def ZXDiagram.getNode? (d : ZXDiagram) (id : NodeId) : Option Node :=
  if h : id < d.nodes.size then d.nodes[id] else none

/-- Add a node, returning the updated diagram and the new node's ID -/
def ZXDiagram.addNode (d : ZXDiagram) (n : Node) : ZXDiagram × NodeId :=
  ({ d with nodes := d.nodes.push (some n) }, d.nodes.size)

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

/-- Remove a node by setting its slot to `none` -/
def ZXDiagram.removeNode (d : ZXDiagram) (n : NodeId) : ZXDiagram :=
  if h : n < d.nodes.size then { d with nodes := d.nodes.set n none } else d

/-- Set a node at a given ID -/
def ZXDiagram.setNode (d : ZXDiagram) (id : NodeId) (n : Node) : ZXDiagram :=
  if h : id < d.nodes.size then { d with nodes := d.nodes.set id (some n) } else d
