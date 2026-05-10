import LeanSpider.Algebraic.ZX
import LeanSpider.Visualize

namespace LeanSpider.Algebraic

open LeanSpider

/-- A partially-built diagram together with its currently-open boundary ports
    and the algebraic-grid `(col, qubit)` position of every node it contains.
    `compose` advances `col`; `stack` advances `qubit`.
    `wireIds` tracks placeholder spider nodes created from `wire`; they are
    spliced out at the end so wires render as plain edges. -/
private structure Frag where
  diagram : ZXDiagram
  left    : List NodeId
  right   : List NodeId
  wireIds : List NodeId
  /-- Number of compose-columns this fragment occupies. -/
  width   : Nat
  /-- Number of stack-qubits this fragment occupies. -/
  height  : Nat
  /-- `(id, col, qubit)` for every node in `diagram`. `col` is `Int` so
      boundary inputs/outputs can sit at -1 / `width`. -/
  pos     : List (NodeId × Int × Nat)

private def Frag.empty : Frag :=
  { diagram := { nodes := [], edges := [] }
    left := [], right := [], wireIds := []
    width := 0, height := 0, pos := [] }

private def shiftEdge (off : Nat) (e : Edge) : Edge :=
  { src := e.src + off, tgt := e.tgt + off }

private def shiftPos (idOff : Nat) (cOff : Int) (qOff : Nat)
    (p : NodeId × Int × Nat) : NodeId × Int × Nat :=
  let (id, c, q) := p
  (id + idOff, c + cOff, q + qOff)

/-- Stack `a` on top of `b` (parallel composition `stack`).
    `b`'s qubits shift down by `a.height`; widths are taken as `max`. -/
private def Frag.append (a b : Frag) : Frag :=
  let off := a.diagram.nodes.length
  { diagram := { nodes := a.diagram.nodes ++ b.diagram.nodes
                 edges := a.diagram.edges ++ b.diagram.edges.map (shiftEdge off) }
    left    := a.left    ++ b.left.map    (· + off)
    right   := a.right   ++ b.right.map   (· + off)
    wireIds := a.wireIds ++ b.wireIds.map (· + off)
    width   := Nat.max a.width b.width
    height  := a.height + b.height
    pos     := a.pos ++ b.pos.map (shiftPos off 0 a.height) }

/-- Sequentially compose `a` then `b`.
    `b`'s columns shift right by `a.width`; heights are taken as `max`. -/
private def Frag.then (a b : Frag) : Frag :=
  let off := a.diagram.nodes.length
  let bLeft  := b.left.map  (· + off)
  let bRight := b.right.map (· + off)
  let bEdges := b.diagram.edges.map (shiftEdge off)
  let connecting := List.zipWith (fun s t => ({ src := s, tgt := t } : Edge)) a.right bLeft
  { diagram := { nodes := a.diagram.nodes ++ b.diagram.nodes
                 edges := a.diagram.edges ++ bEdges ++ connecting }
    left    := a.left
    right   := bRight
    wireIds := a.wireIds ++ b.wireIds.map (· + off)
    width   := a.width + b.width
    height  := Nat.max a.height b.height
    pos     := a.pos ++ b.pos.map (shiftPos off (a.width : Int) 0) }

/-- Build a positioned `Frag` from an algebraic `ZX n m` term. Boundary
    input/output nodes are added later by `ZX.toPositionedDiagram`. -/
private def buildFrag : {n m : Nat} → ZX n m → Frag
  | _, _, .empty    => Frag.empty
  | _, _, .wire     =>
    let (d, id) := Frag.empty.diagram.addNode (.spider .Z ⟨0, 1⟩)
    { diagram := d, left := [id], right := [id], wireIds := [id]
      width := 1, height := 1, pos := [(id, 0, 0)] }
  | _, _, .hadamard =>
    let (d, id) := Frag.empty.diagram.addNode .hadamard
    { diagram := d, left := [id], right := [id], wireIds := []
      width := 1, height := 1, pos := [(id, 0, 0)] }
  | _, _, .spider c n m φ =>
    let (d, id) := Frag.empty.diagram.addNode (.spider c φ)
    { diagram := d, left := List.replicate n id, right := List.replicate m id, wireIds := []
      width := 1, height := Nat.max n m, pos := [(id, 0, 0)] }
  | _, _, .stack a b   => Frag.append (buildFrag a) (buildFrag b)
  | _, _, .compose a b => Frag.then   (buildFrag a) (buildFrag b)

/-- Remove a placeholder wire node by replacing its two incident edges with a
    single bridge edge between its neighbours. Idempotent if `w` is no longer
    present. The wire's position entry stays in the position list but its
    `nodes` slot is set to `none`, so the JSON emitter skips it. -/
private def spliceWire (d : ZXDiagram) (w : NodeId) : ZXDiagram :=
  let other (e : Edge) : NodeId := if e.src == w then e.tgt else e.src
  let (incident, kept) := d.edges.partition (fun e => e.src == w || e.tgt == w)
  match incident with
  | [e₁, e₂] =>
    let bridge : Edge := { src := other e₁, tgt := other e₂ }
    { nodes := d.nodes.set w none, edges := kept ++ [bridge] }
  | _ => d

/-- Convert an algebraic ZX term to a positioned diagram: a `ZXDiagram` plus
    a list of `(NodeId, col, qubit)` triples giving the algebraic-grid
    position of each node. Inputs sit at `col = -1`, outputs at `col = width`,
    each at `qubit = ioId`. Wires are spliced; their entries remain in the
    position list but their node slots are `none`. -/
def ZX.toPositionedDiagram {n m : Nat} (z : ZX n m) :
    ZXDiagram × List (NodeId × Int × Nat) :=
  let f := buildFrag z
  let inputNodes  : List Node := (List.range n).map (fun i => .input i)
  let outputNodes : List Node := (List.range m).map (fun i => .output i)
  let (d₁, ins)  := f.diagram.addNodes inputNodes
  let (d₂, outs) := d₁.addNodes outputNodes
  let inEdges  := List.zipWith (fun s t => ({ src := s, tgt := t } : Edge)) ins f.left
  let outEdges := List.zipWith (fun s t => ({ src := s, tgt := t } : Edge)) f.right outs
  let d₃ := d₂.addEdges (inEdges ++ outEdges)
  let d₄ := f.wireIds.foldl spliceWire d₃
  let inPos : List (NodeId × Int × Nat) :=
    List.zipWith (fun id i => ((id, (-1 : Int), i) : NodeId × Int × Nat)) ins (List.range n)
  let outPos : List (NodeId × Int × Nat) :=
    List.zipWith (fun id i => ((id, (f.width : Int), i) : NodeId × Int × Nat)) outs (List.range m)
  (d₄, f.pos ++ inPos ++ outPos)

/-- The graph-style `ZXDiagram` lowering, identical in result to the previous
    implementation; positions are discarded for callers that don't need them. -/
def ZX.toZXDiagram {n m : Nat} (z : ZX n m) : ZXDiagram :=
  z.toPositionedDiagram.1

-- == Position-aware JSON emission ==
-- Mirrors `Node.toJson` / `ZXDiagram.toJson` from `LeanSpider/Visualize.lean`,
-- adding `col` and `qubit` fields per node so the widget can skip BFS layout.

private def natJson (n : Nat) : Lean.Json := .num { mantissa := ↑n, exponent := 0 }
private def intJson (n : Int) : Lean.Json := .num { mantissa := n, exponent := 0 }

private def nodeToJsonPositioned (n : Node) (idx : Nat) (col : Int) (qubit : Nat) :
    Lean.Json :=
  let posFields : List (String × Lean.Json) := [("col", intJson col), ("qubit", natJson qubit)]
  match n with
  | .spider c p =>
    let color := match c with | .Z => "Z" | .X => "X"
    .mkObj ([("id", natJson idx), ("type", .str "spider"),
             ("color", .str color), ("phase", p.toJson)] ++ posFields)
  | .hadamard =>
    let phase : Phase := ⟨1, 1⟩
    .mkObj ([("id", natJson idx), ("type", .str "hadamard"),
             ("phase", phase.toJson)] ++ posFields)
  | .input id =>
    .mkObj ([("id", natJson idx), ("type", .str "input"), ("ioId", natJson id)] ++ posFields)
  | .output id =>
    .mkObj ([("id", natJson idx), ("type", .str "output"), ("ioId", natJson id)] ++ posFields)

private def lookupPos (pos : List (NodeId × Int × Nat)) (id : NodeId) :
    Option (Int × Nat) :=
  pos.findSome? (fun (i, c, q) => if i == id then some (c, q) else none)

/-- Same JSON shape as `ZXDiagram.toJson`, but every emitted node carries
    `col` and `qubit` fields from `pos`. `none` slots in `nodes` are skipped
    (so spliced wires don't show up). Nodes without an entry in `pos` fall
    back to the un-positioned `Node.toJson` form (defensive — shouldn't
    happen for terms produced by `ZX.toPositionedDiagram`). -/
def _root_.ZXDiagram.toPositionedJson (d : ZXDiagram) (pos : List (NodeId × Int × Nat)) :
    Lean.Json :=
  let nodes := d.nodes.foldl (init := (#[], 0)) fun (acc, idx) opt =>
    match opt with
    | some n =>
      match lookupPos pos idx with
      | some (c, q) => (acc.push (nodeToJsonPositioned n idx c q), idx + 1)
      | none        => (acc.push (n.toJson idx), idx + 1)
    | none => (acc, idx + 1)
  let nodes := nodes.1
  let edges := (d.edges.map Edge.toJson).toArray
  .mkObj [("nodes", .arr nodes), ("edges", .arr edges)]

open ProofWidgets in
/-- Render an algebraic ZX term in the InfoView. Positions come from the
    algebraic structure (`compose` → col, `stack` → qubit), so the widget
    skips its BFS layout. -/
def ZX.toHtml {n m : Nat} (z : ZX n m) : Html :=
  let (d, pos) := z.toPositionedDiagram
  Html.ofComponent ZXWidget ⟨d.toPositionedJson pos, .null⟩ #[]

end LeanSpider.Algebraic
