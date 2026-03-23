import LeanZX.ZXDiagram
import ProofWidgets.Component.HtmlDisplay

open Lean Server ProofWidgets

-- == ZXDiagram JSON serialization (`ZXDiagram` to `Lean.Json`) ==
private def natJson (n : Nat) : Json := .num { mantissa := ↑n, exponent := 0 }

def Phase.toJson (p : Phase) : Json :=
  if p.den == 1 then .str (toString p.num)
  else .str s!"{p.num}/{p.den}"

def Node.toJson (n : Node) (idx : Nat) : Json :=
  match n with
  | .spider c p =>
    let color := match c with | .Z => "Z" | .X => "X"
    .mkObj [("id", natJson idx), ("type", .str "spider"),
            ("color", .str color), ("phase", p.toJson)]
  | .hadamard =>
    -- Default phase for Hadamard box is pi
    let phase: Phase := ⟨1, 1⟩
    .mkObj [("id", natJson idx), ("type", .str "hadamard"),
            ("phase", phase.toJson)]
  | .input id =>
    .mkObj [("id", natJson idx), ("type", .str "input"), ("ioId", natJson id)]
  | .output id =>
    .mkObj [("id", natJson idx), ("type", .str "output"), ("ioId", natJson id)]

def Edge.toJson (e : Edge) : Json :=
  .mkObj [("src", natJson e.src), ("tgt", natJson e.tgt)]

def ZXDiagram.toJson (d : ZXDiagram) : Json :=
  let nodes := d.nodes.foldl (init := (#[], 0)) fun (acc, idx) opt =>
    match opt with
    | some n => (acc.push (n.toJson idx), idx + 1)
    | none   => (acc, idx + 1)
  let nodes := nodes.1
  let edges := (d.edges.map Edge.toJson).toArray
  .mkObj [("nodes", .arr nodes), ("edges", .arr edges)]

-- == ProofWidgets4 widget definition ==
-- Props passed to widget
structure ZXWidgetProps where
  diagram : Json      -- JSON representation of ZXDiagram
  deriving RpcEncodable

-- Widget definition
@[widget_module]
def ZXWidget : Component ZXWidgetProps where
  javascript := include_str ".." / ".lake" / "build" / "js" / "zxDiagram.js"

-- Display a ZXDiagram in the ZXWidget in the InfoView
def ZXDiagram.toHtml (d : ZXDiagram) : Html :=
  Html.ofComponent ZXWidget ⟨d.toJson⟩ #[]
