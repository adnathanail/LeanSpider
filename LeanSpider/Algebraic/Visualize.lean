import LeanSpider.Algebraic.ZX
import LeanSpider.Visualize

namespace LeanSpider.Algebraic

open LeanSpider

/-- A partially-built diagram together with its currently-open boundary ports.
    `left[i]` is the `NodeId` carrying the i-th input port of the fragment;
    `right[i]` similarly for outputs. The same id may appear multiple times
    (e.g. a single spider with 2 outputs has both `right` entries pointing at it). -/
private structure Frag where
  diagram : ZXDiagram
  left  : List NodeId
  right : List NodeId

private def Frag.empty : Frag := { diagram := { nodes := [], edges := [] }, left := [], right := [] }

private def shiftEdge (off : Nat) (e : Edge) : Edge :=
  { src := e.src + off, tgt := e.tgt + off }

/-- Concatenate two fragments side-by-side (parallel composition `stack`). -/
private def Frag.append (a b : Frag) : Frag :=
  let off := a.diagram.nodes.length
  { diagram := { nodes := a.diagram.nodes ++ b.diagram.nodes
                 edges := a.diagram.edges ++ b.diagram.edges.map (shiftEdge off) }
    left  := a.left  ++ b.left.map  (· + off)
    right := a.right ++ b.right.map (· + off) }

/-- Sequentially compose two fragments: wire `a`'s right ports to `b`'s left ports. -/
private def Frag.then (a b : Frag) : Frag :=
  let off := a.diagram.nodes.length
  let bLeft  := b.left.map  (· + off)
  let bRight := b.right.map (· + off)
  let bEdges := b.diagram.edges.map (shiftEdge off)
  let connecting := List.zipWith (fun s t => ({ src := s, tgt := t } : Edge)) a.right bLeft
  { diagram := { nodes := a.diagram.nodes ++ b.diagram.nodes
                 edges := a.diagram.edges ++ bEdges ++ connecting }
    left  := a.left
    right := bRight }

/-- Build a `Frag` from an algebraic `ZX n m` term. Boundary input/output nodes are
    *not* added here — that's done in `ZX.toZXDiagram`. -/
private def buildFrag : {n m : Nat} → ZX n m → Frag
  | _, _, .empty    => Frag.empty
  | _, _, .wire     =>
    -- Identity Z-spider (phase 0, degree 2); cleanly removable via IdentityRemoval.
    let (d, id) := Frag.empty.diagram.addNode (.spider .Z ⟨0, 1⟩)
    { diagram := d, left := [id], right := [id] }
  | _, _, .hadamard =>
    let (d, id) := Frag.empty.diagram.addNode .hadamard
    { diagram := d, left := [id], right := [id] }
  | _, _, .spider c n m φ =>
    let (d, id) := Frag.empty.diagram.addNode (.spider c φ)
    { diagram := d, left := List.replicate n id, right := List.replicate m id }
  | _, _, .stack a b   => Frag.append (buildFrag a) (buildFrag b)
  | _, _, .compose a b => Frag.then   (buildFrag a) (buildFrag b)

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
  d₂.addEdges (inEdges ++ outEdges)

open ProofWidgets in
/-- Render an algebraic ZX term in the InfoView via the existing `ZXWidget`. -/
def ZX.toHtml {n m : Nat} (z : ZX n m) : Html := z.toZXDiagram.toHtml

end LeanSpider.Algebraic
