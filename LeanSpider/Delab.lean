import LeanSpider.ZXDiagram

open Lean PrettyPrinter Delaborator SubExpr

namespace LeanSpider

/-! # Goal display for `ZXDiagram` literals

`applyRewrite` reflects a fully evaluated diagram into the goal, so its node list
is a literal of `Option Node`. The `some`/`none` wrappers carry nothing a reader
wants — what matters is the node, or that the slot is empty — and they dominate
the goal once a diagram has more than a few nodes.

An empty slot is rendered `_` rather than dropped, because node IDs are list
indices: removing empties would silently renumber every node after them, and
those IDs are exactly what gets typed into `zx_sp 1 3` and friends.

The placeholder is a hole and not `·`, which would read better: declaring
`syntax "·" : term` collides with Lean's cdot, breaking `(· + 1)` in every file
that imports this one.
-/

mutual

/-- Render one `Option Node` slot: `some n` as `n`, `none` as `_`. -/
partial def delabNodeSlot : DelabM Term := do
  match (← getExpr).getAppFnArgs with
  | (``Option.some, #[_, _]) => withNaryArg 1 delab
  | (``Option.none, #[_])    => `(_)
  | _                        => failure

/-- Collect a literal `List (Option Node)`. Fails on anything not built from
    `cons`/`nil`, so diagrams over variables fall back to the default display. -/
partial def delabNodeList : DelabM (Array Term) := do
  match (← getExpr).getAppFnArgs with
  | (``List.nil, _)           => return #[]
  | (``List.cons, #[_, _, _]) => do
      let hd ← withNaryArg 1 delabNodeSlot
      let tl ← withNaryArg 2 delabNodeList
      return #[hd] ++ tl
  | _                         => failure

end

@[delab app.ZXDiagram.mk]
def delabZXDiagram : Delab := do
  guard ((← getExpr).getAppNumArgs == 2)
  let nodes ← withNaryArg 0 delabNodeList
  let edges ← withNaryArg 1 delab
  -- Field names are spliced as explicit idents; a plain quotation would render
  -- them hygienically as `nodes✝` and `edges✝`.
  `({ $(mkIdent `nodes):ident := [$nodes,*], $(mkIdent `edges):ident := $edges })

end LeanSpider
