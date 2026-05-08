import LeanSpider.All
import ProofWidgets.Component.HtmlDisplay

open Lean Server ProofWidgets LeanSpider.Algebraic

def algSpider : ZX 1 1 := .spider .Z 1 1 ⟨1, 2⟩
#html algSpider.toHtml

def algFusionLHS : ZX 1 1 := .spider .Z 1 1 ⟨1, 4⟩ ⨾ .spider .Z 1 1 ⟨1, 4⟩
#html algFusionLHS.toHtml

private def natJson (n : Nat) : Json := .num { mantissa := ↑n, exponent := 0 }

def test : Json :=
    .mkObj
      [ ("nodes", .arr #[
          .mkObj [("id", natJson 0), ("type", .str "input"),  ("ioId", natJson 0)],
          .mkObj [("id", natJson 1), ("type", .str "output"), ("ioId", natJson 0)]
        ])
      , ("edges", .arr #[
          .mkObj [("src", natJson 0), ("tgt", natJson 1)]
        ])
      ]


private structure FFrag where
  nodes : List Nat
  edges : List (Nat × Nat)
  inputs : List Nat
  outputs : List Nat

def ZXtoFFrag : {n m : Nat} → ZX n m → FFrag
  | _, _, .spider c n m φ =>
    { nodes := [1, 2, 3], edges := [(1, 2), (2, 3)], inputs := [1], outputs := [3] }
  | _, _, _ => { nodes := [], edges := [], inputs := [], outputs := []}

def FFragtoJson (f: FFrag) : Json :=
  .mkObj
    [ ("nodes", .arr (f.nodes.map (λ n => Lean.Json.mkObj [
          ("id", natJson n),
          ("type", .str "spider"),
          ("color", .str "Z"),
          ("phase", .str s!"{0}/{1}")
        ])).toArray),
      ("edges", .arr (f.edges.map (λ e => Lean.Json.arr #[
          Lean.Json.mkObj [("src", natJson e.fst), ("tgt", natJson e.snd)]
      ])).toArray)
    ]

#eval test
#eval FFragtoJson (ZXtoFFrag algSpider)

def html : Html :=
  Html.ofComponent ZXWidget ⟨FFragtoJson (ZXtoFFrag algSpider), .null⟩ #[]

#html html
