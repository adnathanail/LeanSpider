import ZxLean.ZXDiagram
import ProofWidgets.Component.HtmlDisplay

open Lean Server ProofWidgets

/-! # ZX Diagram Visualization

Serializes a `ZXDiagram` to `Lean.Json` and provides a ProofWidgets4 component
for rendering the diagram in the VS Code InfoView.
-/

-- ============================================================
-- JSON serialization
-- ============================================================

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
  | .input id =>
    .mkObj [("id", natJson idx), ("type", .str "input"), ("ioId", natJson id)]
  | .output id =>
    .mkObj [("id", natJson idx), ("type", .str "output"), ("ioId", natJson id)]

def Edge.toJson (e : Edge) : Json :=
  .mkObj [("src", natJson e.src), ("tgt", natJson e.tgt)]

def ZXDiagram.toJson (d : ZXDiagram) : Json :=
  let nodes := d.nodes.mapIdx fun idx n => n.toJson idx
  let edges := d.edges.map Edge.toJson
  .mkObj [("nodes", .arr nodes), ("edges", .arr edges)]

-- ============================================================
-- ProofWidgets4 widget
-- ============================================================

structure ZXWidgetProps where
  diagram : Json
  deriving RpcEncodable

@[widget_module]
def ZXWidget : Component ZXWidgetProps where
  javascript := include_str ".." / "widget" / "build" / "zxDiagram.js"
