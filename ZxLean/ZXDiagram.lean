import ZxLean.Utils

inductive SpiderColor where
  | Z  -- green
  | X  -- red
  deriving Repr, BEq, DecidableEq

/-- Phase as a rational multiple of π, stored as p/q.
    e.g. phase 1 2 represents π/2 -/
structure Phase where
  num : Int
  den : Nat := 1
  deriving Repr, DecidableEq

-- Simplify a phase: reduce fraction by GCD, then reduce numerator mod 2*den (mod 2π)
def Phase.simplify (p : Phase) : Phase :=
  let g := Int.gcd p.num p.den
  if g == 0 then p
  else
    let num := p.num / g
    let den := p.den / g
    { num := num % (2 * den), den := den }

-- Properly define equality for phases, so that 18/4 == 9/2
instance : BEq Phase where
  beq a b :=
    let a := a.simplify
    let b := b.simplify
    a.num == b.num && a.den == b.den

/-- a/b + c/d = (ad + bc)/bd -/
def Phase.add (p q : Phase) : Phase :=
  { num := p.num * q.den + q.num * p.den
    den := p.den * q.den }

instance : Add Phase where
  add := Phase.add

/-- Internal spider (Z/X) or input or output -/
inductive Node where
  | spider (color : SpiderColor) (phase : Phase)
  | hadamard
  | input  (id : Nat)
  | output (id : Nat)
  deriving Repr, BEq, DecidableEq

/-- Get the color of a node, if it is a spider -/
def Node.color? : Node → Option SpiderColor
  | .spider c _ => some c
  | _ => none

/-- Get the phase of a node, if it is a spider -/
def Node.phase? : Node → Option Phase
  | .spider _ p => some p
  | _ => none

def Node.isHadamard : Node → Bool
  | .hadamard => true
  | _ => false

/-- Stable node identifier -/
abbrev NodeId := Nat

/-- Edge between nodes identified by stable NodeId -/
structure Edge where
  src : NodeId
  tgt : NodeId
  deriving Repr, BEq, DecidableEq

-- Define ordering of edges, so we can sort them,
--   so we can make graph equality not care about edge order
instance : Ord Edge where
  compare a b :=
    match compare a.src b.src with
    | .eq => compare a.tgt b.tgt
    | ord => ord

instance : LT Edge := Ord.toLT inferInstance

/-- Canonicalize an edge so that src ≤ tgt (edges are undirected) -/
def Edge.normalize (e : Edge) : Edge :=
  if e.src ≤ e.tgt then e else { src := e.tgt, tgt := e.src }

structure ZXDiagram where
  nodes : List (Option Node)
  edges : List Edge
  deriving Repr, Inhabited, DecidableEq

-- Make graph equality not care about edge order by sorting the edge lists
instance : BEq ZXDiagram where
  beq a b := a.nodes == b.nodes &&
    a.edges.insertionSort == b.edges.insertionSort

/-- Build a ZXDiagram from lists of nodes (list indices become node IDs) -/
def ZXDiagram.ofList (nodes : List Node) (edges : List Edge) : ZXDiagram :=
  { nodes := nodes.map some, edges := edges }

/-- Look up a node by its stable ID -/
def ZXDiagram.getNode? (d : ZXDiagram) (id : NodeId) : Option Node :=
  d.nodes[id]? |>.join

/-- Add a node, returning the updated diagram and the new node's ID -/
def ZXDiagram.addNode (d : ZXDiagram) (n : Node) : ZXDiagram × NodeId :=
  ({ d with nodes := d.nodes ++ [some n] }, d.nodes.length)

/-- Add an edge between two nodes -/
def ZXDiagram.addEdge (d : ZXDiagram) (e : Edge) : ZXDiagram :=
  { d with edges := d.edges ++ [e] }

/-- Check whether two node IDs are connected by an edge -/
def ZXDiagram.connected (d : ZXDiagram) (a b : NodeId) : Bool :=
  d.edges.any fun e => (e.src == a && e.tgt == b) || (e.src == b && e.tgt == a)

/-- Get all neighbor IDs of a given node -/
def ZXDiagram.neighbors (d : ZXDiagram) (n : NodeId) : List NodeId :=
  d.edges.foldl (init := []) fun acc e =>
    if e.src == n then acc ++ [e.tgt]
    else if e.tgt == n then acc ++ [e.src]
    else acc

/-- Remove all edges touching a given node ID -/
def ZXDiagram.removeEdgesOf (d : ZXDiagram) (n : NodeId) : ZXDiagram :=
  { d with edges := d.edges.filter fun e => e.src != n && e.tgt != n }

/-- Remove a node by setting its slot to `none` -/
def ZXDiagram.removeNode (d : ZXDiagram) (n : NodeId) : ZXDiagram :=
  { d with nodes := d.nodes.set n none }

/-- Set a node at a given ID -/
def ZXDiagram.setNode (d : ZXDiagram) (id : NodeId) (n : Node) : ZXDiagram :=
  { d with nodes := d.nodes.set id (some n) }

/-- Normalize a diagram: canonicalize edge direction, sort edges, and simplify phases -/
def ZXDiagram.normalize (d : ZXDiagram) : ZXDiagram :=
  { nodes := d.nodes.map fun
      | some (.spider c p) => some (.spider c p.simplify)
      | n => n
    edges := (d.edges.map Edge.normalize).insertionSort }
