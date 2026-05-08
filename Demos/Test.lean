import LeanSpider.All
import ProofWidgets.Component.HtmlDisplay

open Lean Server ProofWidgets LeanSpider.Algebraic

def algSpider : ZX 1 1 := .spider .Z 1 1 ⟨1, 2⟩
#html algSpider.toHtml

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

def ZXtoJson : {n m : Nat} → ZX n m → Json
  | _, _, .spider c n m φ =>
    .mkObj
      [ ("nodes", .arr #[
          .mkObj [
            ("id", natJson 0),
            ("type", .str "spider"),
            ("color", match c with | .Z => "Z" | .X => "X"),
            ("phase", φ.toJson)
          ],
        ])
      , ("edges", .arr #[])
      ]
  | _, _, _ => .mkObj []

#eval test

def html : Html :=
  Html.ofComponent ZXWidget ⟨ZXtoJson algSpider, .null⟩ #[]

#html html
