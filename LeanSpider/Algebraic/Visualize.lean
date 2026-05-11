import LeanSpider.Algebraic.ZX
import LeanSpider.Visualize

namespace LeanSpider.Algebraic

open LeanSpider

/-- The set of node ids inside a `stack` or `compose` subtree, drawn behind
    the diagram as a bounding rectangle. The widget computes pixel bounds
    from each node's live position so boxes follow drags and don't extend
    into spliced-wire empty space. `kind` is "stack" or "compose". -/
structure BoxRecord where
  kind    : String
  nodeIds : List NodeId
  deriving Repr

/-- A partially-built diagram together with its currently-open boundary ports
    (each paired with the qubit-in-halves at which the port enters/leaves the
    body) and the algebraic-grid `(col, qubitHalves)` position of every node
    it contains. Qubit positions are stored as `2 ×` the actual qubit so a
    spider with mismatched arity (e.g. `Z 1→2`) can sit on a half-row at the
    centre of its span. The structural `height` stays a count of integer
    slots; `compose` advances `col`, `stack` advances `qubitHalves` by
    `2 * a.height`. `boxes` records bounding rectangles for every
    `stack`/`compose` subtree so the widget can draw them behind the diagram. -/
private structure Frag where
  diagram : ZXDiagram
  /-- Each open input port: `(node id it connects to, qubitHalves at which
      it enters the body)`. Top-level inputs inherit this qubit, so a
      boundary connected to a spider centre lands on the same half-row. -/
  left    : List (NodeId × Nat)
  /-- Each open output port: `(node id it leaves from, qubitHalves at which
      it exits the body)`. -/
  right   : List (NodeId × Nat)
  /-- Number of compose-columns this fragment occupies. -/
  width   : Nat
  /-- Number of stack-qubit-slots this fragment occupies (NOT halves). -/
  height  : Nat
  /-- `(id, col, qubitHalves)` for every node in `diagram`. `col` is `Int` so
      boundary inputs/outputs can sit at -1 / `width`; the third component
      is `2 ×` the real qubit. -/
  pos     : List (NodeId × Int × Nat)
  /-- One entry per `stack`/`compose` subtree, in this fragment's local
      grid coordinates. Empty for leaves. -/
  boxes   : List BoxRecord

private def Frag.empty : Frag :=
  { diagram := { nodes := [], edges := [] }
    left := [], right := []
    width := 0, height := 0, pos := [], boxes := [] }

private def shiftEdge (off : Nat) (e : Edge) : Edge :=
  { src := e.src + off, tgt := e.tgt + off }

private def shiftPort (idOff qOff : Nat) (p : NodeId × Nat) : NodeId × Nat :=
  let (id, q) := p
  (id + idOff, q + qOff)

private def shiftPos (idOff : Nat) (cOff : Int) (qOff : Nat)
    (p : NodeId × Int × Nat) : NodeId × Int × Nat :=
  let (id, c, q) := p
  (id + idOff, c + cOff, q + qOff)

private def shiftBoxIds (idOff : Nat) (b : BoxRecord) : BoxRecord :=
  { b with nodeIds := b.nodeIds.map (· + idOff) }

/-- Stack `a` on top of `b` (parallel composition `stack`).
    `b`'s qubits shift down by `2 * a.height` (in halves); widths are taken
    as `max`. Records a "stack" box covering the union of subtree node ids. -/
private def Frag.append (a b : Frag) : Frag :=
  let off := a.diagram.nodes.length
  let qOff := 2 * a.height
  let allIds : List NodeId :=
    a.pos.map (·.1) ++ (b.pos.map (·.1)).map (· + off)
  let newBox : List BoxRecord :=
    if allIds.isEmpty then [] else [{ kind := "stack", nodeIds := allIds }]
  { diagram := { nodes := a.diagram.nodes ++ b.diagram.nodes
                 edges := a.diagram.edges ++ b.diagram.edges.map (shiftEdge off) }
    left    := a.left    ++ b.left.map    (shiftPort off qOff)
    right   := a.right   ++ b.right.map   (shiftPort off qOff)
    width   := Nat.max a.width b.width
    height  := a.height + b.height
    pos     := a.pos ++ b.pos.map (shiftPos off 0 qOff)
    boxes   := a.boxes ++ b.boxes.map (shiftBoxIds off) ++ newBox }

/-- Sequentially compose `a` then `b`.
    `b`'s columns shift right by `a.width`; heights are taken as `max`.
    Records a "compose" box covering the union of subtree node ids. -/
private def Frag.then (a b : Frag) : Frag :=
  let off := a.diagram.nodes.length
  let bLeft  := b.left.map  (shiftPort off 0)
  let bRight := b.right.map (shiftPort off 0)
  let bEdges := b.diagram.edges.map (shiftEdge off)
  let connecting := List.zipWith
    (fun s t => ({ src := s.1, tgt := t.1 } : Edge)) a.right bLeft
  let allIds : List NodeId :=
    a.pos.map (·.1) ++ (b.pos.map (·.1)).map (· + off)
  let newBox : List BoxRecord :=
    if allIds.isEmpty then [] else [{ kind := "compose", nodeIds := allIds }]
  { diagram := { nodes := a.diagram.nodes ++ b.diagram.nodes
                 edges := a.diagram.edges ++ bEdges ++ connecting }
    left    := a.left
    right   := bRight
    width   := a.width + b.width
    height  := Nat.max a.height b.height
    pos     := a.pos ++ b.pos.map (shiftPos off (a.width : Int) 0)
    boxes   := a.boxes ++ b.boxes.map (shiftBoxIds off) ++ newBox }

/-- Build a positioned `Frag` from an algebraic `ZX n m` term. Boundary
    input/output nodes are added later by `ZX.toPositionedDiagram`. -/
private def buildFrag : {n m : Nat} → ZX n m → Frag
  | _, _, .empty    => Frag.empty
  | _, _, .wire     =>
    let (d, id) := Frag.empty.diagram.addNode .wire
    { diagram := d, left := [(id, 0)], right := [(id, 0)]
      width := 1, height := 1, pos := [(id, 0, 0)], boxes := [] }
  | _, _, .hadamard =>
    let (d, id) := Frag.empty.diagram.addNode .hadamard
    { diagram := d, left := [(id, 0)], right := [(id, 0)]
      width := 1, height := 1, pos := [(id, 0, 0)], boxes := [] }
  | _, _, .spider c n m φ =>
    let (d, id) := Frag.empty.diagram.addNode (.spider c φ)
    let mx := Nat.max n m
    -- `centre` is the qubitHalves at the midpoint of slots `0..mx-1`.
    -- `mx - 1` saturates at 0 when `mx = 0` (a 0-leg spider has no ports).
    let centre := mx - 1
    let portQubits (k : Nat) : List Nat :=
      if k = 1 then [centre] else (List.range k).map (fun i => 2 * i)
    let leftPorts  := (portQubits n).map (fun q => (id, q))
    let rightPorts := (portQubits m).map (fun q => (id, q))
    { diagram := d, left := leftPorts, right := rightPorts
      width := 1, height := mx, pos := [(id, 0, centre)], boxes := [] }
  | _, _, .stack a b   => Frag.append (buildFrag a) (buildFrag b)
  | _, _, .compose a b => Frag.then   (buildFrag a) (buildFrag b)

/-- Convert an algebraic ZX term to a positioned diagram: a `ZXDiagram`, a
    list of `(NodeId, col, qubitHalves)` triples giving the algebraic-grid
    position of each node (qubit positions are `2 ×` the real qubit so
    half-rows are representable), and a list of `BoxRecord`s describing the
    bounding rectangle of every `stack`/`compose` subtree. Inputs sit at
    `col = -1` and outputs at `col = width`, each at the qubit of the body
    port they connect to (so e.g. an input feeding a `Z 1→2` spider sits at
    the spider's centred half-row). Wires render as `.wire` nodes (drawn as
    small dots in the widget). -/
def ZX.toPositionedDiagram {n m : Nat} (z : ZX n m) :
    ZXDiagram × List (NodeId × Int × Nat) × List BoxRecord :=
  let f := buildFrag z
  let inputNodes  : List Node := (List.range n).map (fun i => .input i)
  let outputNodes : List Node := (List.range m).map (fun i => .output i)
  let (d₁, ins)  := f.diagram.addNodes inputNodes
  let (d₂, outs) := d₁.addNodes outputNodes
  let inEdges  := List.zipWith
    (fun s p => ({ src := s, tgt := p.1 } : Edge)) ins f.left
  let outEdges := List.zipWith
    (fun p t => ({ src := p.1, tgt := t } : Edge)) f.right outs
  let d₃ := d₂.addEdges (inEdges ++ outEdges)
  let inPos : List (NodeId × Int × Nat) :=
    List.zipWith (fun id p => ((id, (-1 : Int), p.2) : NodeId × Int × Nat))
      ins f.left
  let outPos : List (NodeId × Int × Nat) :=
    List.zipWith (fun id p => ((id, (f.width : Int), p.2) : NodeId × Int × Nat))
      outs f.right
  (d₃, f.pos ++ inPos ++ outPos, f.boxes)

/-- The graph-style `ZXDiagram` lowering, identical in result to the previous
    implementation; positions and boxes are discarded for callers that don't
    need them. -/
def ZX.toZXDiagram {n m : Nat} (z : ZX n m) : ZXDiagram :=
  z.toPositionedDiagram.1

-- == Position-aware JSON emission ==
-- Mirrors `Node.toJson` / `ZXDiagram.toJson` from `LeanSpider/Visualize.lean`,
-- adding `col`/`qubit` per node and a top-level `boxes` array.

private def natJson (n : Nat) : Lean.Json := .num { mantissa := ↑n, exponent := 0 }
private def intJson (n : Int) : Lean.Json := .num { mantissa := n, exponent := 0 }
/-- Emit a qubit-in-halves as a JSON real number: e.g. `1` → `0.5`, `2` → `1`,
    `3` → `1.5`. The widget reads `qubit` as a plain `number`. -/
-- `Lean.JsonNumber` stores the value as `mantissa * 10 ^ -exponent`, with
-- `exponent : Nat`. So `mantissa = 5h, exponent = 1` gives `h/2`.
private def halfJson (h : Nat) : Lean.Json :=
  .num { mantissa := (h : Int) * 5, exponent := 1 }

private def nodeToJsonPositioned (n : Node) (idx : Nat) (col : Int) (qubit : Nat) :
    Lean.Json :=
  let posFields : List (String × Lean.Json) := [("col", intJson col), ("qubit", halfJson qubit)]
  match n with
  | .spider c p =>
    let color := match c with | .Z => "Z" | .X => "X"
    .mkObj ([("id", natJson idx), ("type", .str "spider"),
             ("color", .str color), ("phase", p.toJson)] ++ posFields)
  | .hadamard =>
    let phase : Phase := ⟨1, 1⟩
    .mkObj ([("id", natJson idx), ("type", .str "hadamard"),
             ("phase", phase.toJson)] ++ posFields)
  | .wire =>
    .mkObj ([("id", natJson idx), ("type", .str "wire")] ++ posFields)
  | .input id =>
    .mkObj ([("id", natJson idx), ("type", .str "input"), ("ioId", natJson id)] ++ posFields)
  | .output id =>
    .mkObj ([("id", natJson idx), ("type", .str "output"), ("ioId", natJson id)] ++ posFields)

private def lookupPos (pos : List (NodeId × Int × Nat)) (id : NodeId) :
    Option (Int × Nat) :=
  pos.findSome? (fun (i, c, q) => if i == id then some (c, q) else none)

private def boxToJson (b : BoxRecord) : Lean.Json :=
  .mkObj [("kind", .str b.kind),
          ("nodeIds", .arr (b.nodeIds.map natJson).toArray)]

/-- Emit the algebraic-positioned diagram as JSON: same shape as
    `ZXDiagram.toJson` plus per-node `col`/`qubit` fields and a top-level
    `boxes` array. -/
private def algebraicJson (d : ZXDiagram) (pos : List (NodeId × Int × Nat))
    (boxes : List BoxRecord) : Lean.Json :=
  let nodes := d.nodes.foldl (init := (#[], 0)) fun (acc, idx) opt =>
    match opt with
    | some n =>
      match lookupPos pos idx with
      | some (c, q) => (acc.push (nodeToJsonPositioned n idx c q), idx + 1)
      | none        => (acc.push (n.toJson idx), idx + 1)
    | none => (acc, idx + 1)
  let nodes := nodes.1
  let edges := (d.edges.map Edge.toJson).toArray
  let boxesJson := (boxes.map boxToJson).toArray
  .mkObj [("nodes", .arr nodes), ("edges", .arr edges), ("boxes", .arr boxesJson)]

open ProofWidgets in
/-- Render an algebraic ZX term in the InfoView. Positions come from the
    algebraic structure (`compose` → col, `stack` → qubit), and bounding
    boxes are emitted for every `stack`/`compose` subtree. -/
def ZX.toHtml {n m : Nat} (z : ZX n m) : Html :=
  let (d, pos, boxes) := z.toPositionedDiagram
  Html.ofComponent ZXWidget ⟨algebraicJson d pos boxes, .null⟩ #[]

open ProofWidgets in
/-- Render two algebraic ZX terms side-by-side in the InfoView — the first
    appears in the `Current` panel, the second in the `Goal` panel. Both
    sides share the same arity so the widget renders them at equal scale. -/
def ZX.toHtmlPair {n m : Nat} (z g : ZX n m) : Html :=
  let (d,  pos,  boxes)  := z.toPositionedDiagram
  let (gd, gpos, gboxes) := g.toPositionedDiagram
  Html.ofComponent ZXWidget
    ⟨algebraicJson d pos boxes, algebraicJson gd gpos gboxes⟩ #[]

end LeanSpider.Algebraic
