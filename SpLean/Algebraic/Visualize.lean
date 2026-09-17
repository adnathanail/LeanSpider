import SpLean.Algebraic.ZX
import SpLean.Widget

/-! # Drawing an algebraic `ZX n m`

`ZXSkel → SpLean.Wire` lowering
- supplies a position for every node
- derived from the term's structure rather than from a layout pass
- zxcc skips BFS so that the picture mirrors the algebra.
-/

namespace SpLean.Algebraic

open SpLean

/-- Index into a fragment's node list, and the node's wire-format `id`. -/
private abbrev NodeId := Nat

/-- An arity-erased mirror of `ZX n m` whose spiders carry the *text* to draw
    rather than a phase value.

    Erasing the arity is what lets the renderer accept a term it cannot
    evaluate: `SpLean/Algebraic/Render.lean` builds a skeleton straight from
    an `Expr` — the only way one is ever built — and a phase argument that is
    a variable becomes the string `"α"` where a closed one becomes `"π/4"`.
    Both are equally drawable, and by the time a phase is here the difference
    has stopped mattering — which is why this carries a `String` and not an
    `AlgPhase`. -/
inductive ZXSkel where
  | empty
  | wire
  | hadamard
  | spider (c : AlgSpColor) (n m : Nat) (phase : String)
  | swap
  | stack (a b : ZXSkel)
  | compose (a b : ZXSkel)
  deriving Repr, Inhabited

def AlgSpColor.wireName : AlgSpColor → String
  | .Z => "Z" | .X => "X"

/-- What a node in the diagram under construction draws as. -/
private inductive NodeShape where
  | spider (c : AlgSpColor) (phase : String)
  | hadamard
  | wire
  | input (ioId : Nat)
  | output (ioId : Nat)

/-- A node together with its algebraic-grid position.

    `qubitHalves` is `2 ×` the real qubit, so a spider with mismatched arity
    (e.g. `Z 1→2`) can sit on the half-row at the centre of its span. The walk
    counts in halves throughout and only `toWire` divides by two. -/
private structure PlacedNode where
  shape : NodeShape
  col : Int
  qubitHalves : Nat

/-- A Hadamard box carries a phase of π by convention. It is sent explicitly,
    like every other phase — see `Wire.Node.phase`. -/
def hadamardPhase : AlgPhase := π

private def PlacedNode.toWire (p : PlacedNode) (id : NodeId) : Wire.Node :=
  let base : Wire.Node :=
    match p.shape with
    | .spider c phase => { id, kind := .spider, color := some c.wireName, phase := some phase }
    | .hadamard    => { id, kind := .hadamard, phase := some hadamardPhase.format }
    | .wire        => { id, kind := .wire }
    | .input ioId  => { id, kind := .input,  ioId := some ioId }
    | .output ioId => { id, kind := .output, ioId := some ioId }
  { base with col := some p.col, qubit := some (Wire.qubitOfHalves p.qubitHalves) }

/-- A partially-built diagram together with its currently-open boundary ports.

    Node ids are list indices into `nodes`, so concatenating two fragments
    renumbers the second by exactly the length of the first. Each open port is
    paired with the qubit-in-halves at which it enters or leaves the body, so
    a top-level boundary can inherit it and meet the body head-on instead of
    jumping diagonally. `height` is a count of whole qubit slots, not halves;
    `compose` advances `col`, `stack` advances `qubitHalves` by `2 * height`.
    `boxes` records a rectangle for every `stack`/`compose` subtree. -/
private structure Frag where
  nodes : List PlacedNode
  edges : List Wire.Edge
  /-- Each open input port: `(node id it connects to, qubitHalves)`. -/
  left : List (NodeId × Nat)
  /-- Each open output port: `(node id it leaves from, qubitHalves)`. -/
  right : List (NodeId × Nat)
  /-- Number of compose-columns this fragment occupies. -/
  width : Nat
  /-- Number of stack-qubit-slots this fragment occupies (NOT halves). -/
  height : Nat
  /-- One entry per `stack`/`compose` subtree. Empty for leaves. -/
  boxes : List Wire.Box

private def Frag.empty : Frag :=
  { nodes := [], edges := [], left := [], right := [],
    width := 0, height := 0, boxes := [] }

/-- A leaf holding one node: a `wire` dot or a Hadamard box. Wires stay real
    nodes so that the `stack`/`compose` boxes around them are non-empty and a
    subtree's drawn extent matches its algebraic shape. -/
private def Frag.leaf (shape : NodeShape) : Frag :=
  { Frag.empty with
    nodes := [{ shape, col := 0, qubitHalves := 0 }]
    left := [(0, 0)], right := [(0, 0)], width := 1, height := 1 }

/-- The swap: two `wire` dots, one per qubit row,
    with outputs linked to the other qubit -/
private def Frag.swap : Frag :=
  { nodes := [{ shape := .wire, col := 0, qubitHalves := 0 },
              { shape := .wire, col := 0, qubitHalves := 2 }]
    edges := []
    left := [(0, 0), (1, 2)]
    right := [(1, 0), (0, 2)]
    width := 1, height := 2, boxes := [] }

private def shiftEdge (off : Nat) (e : Wire.Edge) : Wire.Edge :=
  { src := e.src + off, tgt := e.tgt + off }

private def shiftPort (idOff qOff : Nat) (p : NodeId × Nat) : NodeId × Nat :=
  (p.1 + idOff, p.2 + qOff)

private def shiftNode (cOff : Int) (qOff : Nat) (p : PlacedNode) : PlacedNode :=
  { p with col := p.col + cOff, qubitHalves := p.qubitHalves + qOff }

private def shiftBox (idOff : Nat) (b : Wire.Box) : Wire.Box :=
  { b with nodeIds := b.nodeIds.map (· + idOff) }

/-- A box over every node of a fragment of `count` nodes, or nothing at all if
    it has none. -/
private def wholeBox (kind : Wire.BoxKind) (count : Nat) : List Wire.Box :=
  if count == 0 then [] else [{ kind, nodeIds := List.range count }]

/-- Stack `a` on top of `b` (parallel composition). `b`'s qubits shift down by
    `2 * a.height` (in halves); widths are taken as `max`. -/
private def Frag.append (a b : Frag) : Frag :=
  let off := a.nodes.length
  let qOff := 2 * a.height
  { nodes := a.nodes ++ b.nodes.map (shiftNode 0 qOff)
    edges := a.edges ++ b.edges.map (shiftEdge off)
    left := a.left ++ b.left.map (shiftPort off qOff)
    right := a.right ++ b.right.map (shiftPort off qOff)
    width := Nat.max a.width b.width
    height := a.height + b.height
    boxes := a.boxes ++ b.boxes.map (shiftBox off)
               ++ wholeBox .stack (off + b.nodes.length) }

/-- Sequentially compose `a` then `b`: connect `a`'s open outputs to `b`'s open
    inputs by id (their qubits need not match), shifting `b` right by `a.width`
    columns. Heights are taken as `max`. -/
private def Frag.then (a b : Frag) : Frag :=
  let off := a.nodes.length
  let bLeft := b.left.map (shiftPort off 0)
  let connecting := List.zipWith
    (fun s t => ({ src := s.1, tgt := t.1 } : Wire.Edge)) a.right bLeft
  { nodes := a.nodes ++ b.nodes.map (shiftNode (a.width : Int) 0)
    edges := a.edges ++ b.edges.map (shiftEdge off) ++ connecting
    left := a.left
    right := b.right.map (shiftPort off 0)
    width := a.width + b.width
    height := Nat.max a.height b.height
    boxes := a.boxes ++ b.boxes.map (shiftBox off)
               ++ wholeBox .compose (off + b.nodes.length) }

/-- Lay a skeleton out. Boundary nodes are added afterwards, by `toWire`. -/
private def buildFrag : ZXSkel → Frag
  | .empty       => Frag.empty
  | .wire        => Frag.leaf .wire
  | .hadamard    => Frag.leaf .hadamard
  | .spider c n m phase =>
    let mx := Nat.max n m
    -- `centre` is the qubitHalves at the midpoint of slots `0..mx-1`.
    -- `mx - 1` saturates at 0 when `mx = 0` (a 0-leg spider has no ports).
    let centre := mx - 1
    -- A lone port sits at the centre, so a single-leg connection is
    -- horizontal; two or more occupy whole slots `0, 2, …, 2(k-1)`.
    let portQubits (k : Nat) : List Nat :=
      if k = 1 then [centre] else (List.range k).map (fun i => 2 * i)
    { nodes := [{ shape := .spider c phase, col := 0, qubitHalves := centre }]
      edges := []
      left := (portQubits n).map (fun q => (0, q))
      right := (portQubits m).map (fun q => (0, q))
      width := 1, height := mx, boxes := [] }
  | .swap        => Frag.swap
  | .stack a b   => Frag.append (buildFrag a) (buildFrag b)
  | .compose a b => Frag.then   (buildFrag a) (buildFrag b)

/-- Lower a skeleton to the wire format.

    Boundary `input`/`output` nodes are added **only** here, at the top level;
    fragments stay arity-pure during the walk. Each boundary inherits the
    qubit of the body port it connects to — so an input feeding a `Z 1→2`
    spider lands on that spider's centred half-row, and one feeding a wire
    pushed down by a sibling `stack` lands at the wire's shifted qubit. The
    arity comes from the fragment's own open ports; the skeleton has no index
    to read it off. -/
def ZXSkel.toWire (z : ZXSkel) : Wire.Diagram :=
  let f := buildFrag z
  let body := f.nodes.length
  let ins := (List.range f.left.length).map (· + body)
  let outs := (List.range f.right.length).map (· + body + f.left.length)
  let inNodes := List.zipWith
    (fun i p => ({ shape := .input i, col := -1, qubitHalves := p.2 } : PlacedNode))
    (List.range f.left.length) f.left
  let outNodes := List.zipWith
    (fun i p => ({ shape := .output i, col := (f.width : Int), qubitHalves := p.2 } : PlacedNode))
    (List.range f.right.length) f.right
  let inEdges := List.zipWith
    (fun id p => ({ src := id, tgt := p.1 } : Wire.Edge)) ins f.left
  let outEdges := List.zipWith
    (fun p id => ({ src := p.1, tgt := id } : Wire.Edge)) f.right outs
  let nodes := f.nodes ++ inNodes ++ outNodes
  { nodes := List.zipWith PlacedNode.toWire nodes (List.range nodes.length)
    edges := f.edges ++ inEdges ++ outEdges
    boxes := f.boxes }

open ProofWidgets in
/-- Display a skeleton in the InfoView. -/
def ZXSkel.toHtml (z : ZXSkel) : Html := z.toWire.toHtml

end SpLean.Algebraic
