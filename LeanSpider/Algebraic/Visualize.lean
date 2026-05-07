import LeanSpider.Algebraic.ZX
import LeanSpider.Visualize

namespace LeanSpider.Algebraic

open LeanSpider

/-- A partially-built diagram together with its currently-open boundary ports.
    `left[i]` is the `NodeId` carrying the i-th input port of the fragment;
    `right[i]` similarly for outputs. The same id may appear multiple times
    (e.g. a single spider with 2 outputs has both `right` entries pointing at it).
    `wireIds` tracks placeholder spider nodes created from `wire` constructors;
    they are spliced out (replaced by a single edge between their two neighbours)
    at the end so wires render as plain edges, not as identity Z-spiders. -/
private structure Frag where
  diagram : ZXDiagram
  left    : List NodeId
  right   : List NodeId
  wireIds : List NodeId

private def Frag.empty : Frag :=
  { diagram := { nodes := [], edges := [] }, left := [], right := [], wireIds := [] }

private def shiftEdge (off : Nat) (e : Edge) : Edge :=
  { src := e.src + off, tgt := e.tgt + off }

/-- Concatenate two fragments side-by-side (parallel composition `stack`). -/
private def Frag.append (a b : Frag) : Frag :=
  let off := a.diagram.nodes.length
  { diagram := { nodes := a.diagram.nodes ++ b.diagram.nodes
                 edges := a.diagram.edges ++ b.diagram.edges.map (shiftEdge off) }
    left    := a.left    ++ b.left.map    (· + off)
    right   := a.right   ++ b.right.map   (· + off)
    wireIds := a.wireIds ++ b.wireIds.map (· + off) }

/-- Sequentially compose two fragments: wire `a`'s right ports to `b`'s left ports. -/
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
    wireIds := a.wireIds ++ b.wireIds.map (· + off) }

/-- Build a `Frag` from an algebraic `ZX n m` term. Boundary input/output nodes are
    *not* added here — that's done in `ZX.toZXDiagram`. -/
private def buildFrag : {n m : Nat} → ZX n m → Frag
  | _, _, .empty    => Frag.empty
  | _, _, .wire     =>
    -- Placeholder Z-spider; spliced out by `spliceWires` so wires render as plain edges.
    let (d, id) := Frag.empty.diagram.addNode (.spider .Z ⟨0, 1⟩)
    { diagram := d, left := [id], right := [id], wireIds := [id] }
  | _, _, .hadamard =>
    let (d, id) := Frag.empty.diagram.addNode .hadamard
    { diagram := d, left := [id], right := [id], wireIds := [] }
  | _, _, .spider c n m φ =>
    let (d, id) := Frag.empty.diagram.addNode (.spider c φ)
    { diagram := d, left := List.replicate n id, right := List.replicate m id, wireIds := [] }
  | _, _, .stack a b   => Frag.append (buildFrag a) (buildFrag b)
  | _, _, .compose a b => Frag.then   (buildFrag a) (buildFrag b)

/-- Remove a placeholder wire node by replacing its two incident edges with a single
    edge between its neighbours. Idempotent if `w` is no longer present. -/
private def spliceWire (d : ZXDiagram) (w : NodeId) : ZXDiagram :=
  let other (e : Edge) : NodeId := if e.src == w then e.tgt else e.src
  let (incident, kept) := d.edges.partition (fun e => e.src == w || e.tgt == w)
  match incident with
  | [e₁, e₂] =>
    let bridge : Edge := { src := other e₁, tgt := other e₂ }
    { nodes := d.nodes.set w none, edges := kept ++ [bridge] }
  | _ => d

/-- Convert an algebraic ZX term to a graph-style `ZXDiagram` for rendering.
    Adds `n` input boundary nodes and `m` output boundary nodes wired to the
    fragment's open ports. -/
def ZX.toZXDiagram {n m : Nat} (z : ZX n m) : ZXDiagram :=
  let f := buildFrag z
  let inputNodes  : List Node := (List.range n).map (fun i => .input i)
  let outputNodes : List Node := (List.range m).map (fun i => .output i)
  let (d₁, ins)  := f.diagram.addNodes inputNodes
  let (d₂, outs) := d₁.addNodes outputNodes
  let inEdges  := List.zipWith (fun s t => ({ src := s, tgt := t } : Edge)) ins f.left
  let outEdges := List.zipWith (fun s t => ({ src := s, tgt := t } : Edge)) f.right outs
  let d₃ := d₂.addEdges (inEdges ++ outEdges)
  f.wireIds.foldl spliceWire d₃

open ProofWidgets in
/-- Render an algebraic ZX term in the InfoView via the existing `ZXWidget`. -/
def ZX.toHtml {n m : Nat} (z : ZX n m) : Html := z.toZXDiagram.toHtml

end LeanSpider.Algebraic
