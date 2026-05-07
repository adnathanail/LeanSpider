import LeanSpider.ZXDiagram

namespace LeanSpider.Algebraic

/-- A free-algebra ZX term, indexed by its arity (`n` inputs, `m` outputs).
    Reuses `SpiderColor` and `Phase` from the graph-style `ZXDiagram` module. -/
inductive ZX : Nat → Nat → Type
  | empty    : ZX 0 0
  | wire     : ZX 1 1
  | hadamard : ZX 1 1
  | spider   : SpiderColor → (n m : Nat) → Phase → ZX n m
  | stack    {n m p q : Nat} : ZX n m → ZX p q → ZX (n + p) (m + q)
  | compose  {n m k : Nat} : ZX n m → ZX m k → ZX n k

/-- Sequential composition: `a ⨾ b` feeds the outputs of `a` into the inputs of `b`. -/
scoped infixl:55 " ⨾ " => ZX.compose

/-- Parallel composition (stacking): `a ⊗ZX b` puts `a` and `b` side by side. -/
scoped infixl:60 " ⊗ZX " => ZX.stack

end LeanSpider.Algebraic
