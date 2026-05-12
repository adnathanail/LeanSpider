import LeanSpider.ZXDiagram
import ProofWidgets.Component.HtmlDisplay

open Lean Server ProofWidgets

-- == ZXDiagram JSON serialization (`ZXDiagram` to `Lean.Json`) ==
private def natJson (n : Nat) : Json := .num { mantissa := ↑n, exponent := 0 }

/-- Human-readable phase string used by the widget. gcd + mod-2π normalize
    via `Phase.simplify`, then format as `π/2`, `-π/4`, `2π/3`, `π`, or `0`.
    Single source of truth for phase display — both the closed-phase JSON
    field (`Phase.toJson` below) and the symbolic-phase label walker in
    `LeanSpider/Algebraic/Tactics.lean` route through this. -/
def Phase.format (p : Phase) : String :=
  let p := p.simplify
  if p.num == 0 then "0"
  else
    let ns := if p.num == 1 then "" else if p.num == -1 then "-"
              else toString p.num
    let ds := if p.den.val == 1 then "" else s!"/{p.den.val}"
    s!"{ns}π{ds}"

def Phase.toJson (p : Phase) : Json := .str p.format

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
  | .wire =>
    .mkObj [("id", natJson idx), ("type", .str "wire")]
  | .input id =>
    .mkObj [("id", natJson idx), ("type", .str "input"), ("ioId", natJson id)]
  | .output id =>
    .mkObj [("id", natJson idx), ("type", .str "output"), ("ioId", natJson id)]

def Edge.toJson (e : Edge) : Json :=
  .mkObj [("src", natJson e.src), ("tgt", natJson e.tgt)]

def ZXDiagram.toJson (d : ZXDiagram) (includeNones : Bool := false) : Json :=
  let nodes := d.nodes.foldl (init := (#[], 0)) fun (acc, idx) opt =>
    match opt with
    | some n => (acc.push (n.toJson idx), idx + 1)
    | none   =>
      -- Display nones in JSON, for zx_debug
      if includeNones then
        (acc.push (.mkObj [("id", natJson idx), ("type", .str "none")]), idx + 1)
      else (acc, idx + 1)
  let nodes := nodes.1
  let edges := (d.edges.map Edge.toJson).toArray
  .mkObj [("nodes", .arr nodes), ("edges", .arr edges)]

-- == ProofWidgets4 widget definition ==
-- Props passed to widget
structure ZXWidgetProps where
  diagram : Json      -- JSON representation of ZXDiagram
  goal : Json := .null -- optional goal diagram (null = not shown)
  deriving RpcEncodable

-- Widget definition
@[widget_module]
def ZXWidget : Component ZXWidgetProps where
  javascript := include_str ".." / ".lake" / "build" / "js" / "zxDiagram.js"

-- Display a ZXDiagram in the ZXWidget in the InfoView
def ZXDiagram.toHtml (d : ZXDiagram) (goal? : Option ZXDiagram := none) : Html :=
  let goalJson := match goal? with
    | some g => g.toJson
    | none   => .null
  Html.ofComponent ZXWidget ⟨d.toJson, goalJson⟩ #[]
