import SpLean.Algebraic.AlgPhase

namespace SpLean.Algebraic

/-- Separate copy of `SpiderColor` from `SpLean/Axiomatic/ZXDiagram.lean`
    Seems neat to just have them fully separate data structures -/
inductive AlgSpColor where
  | Z  -- green
  | X  -- red
  deriving Repr, BEq, DecidableEq

/-- A free-algebra ZX term, indexed by its arity (`n` inputs, `m` outputs). -/
inductive ZX : Nat → Nat → Type
  | empty    : ZX 0 0
  | wire     : ZX 1 1
  | hadamard : ZX 1 1
  | spider   (c : AlgSpColor) (n m : Nat) (φ : AlgPhase := 0) : ZX n m
  | swap     : ZX 2 2
  | stack    {n m p q : Nat} : ZX n m → ZX p q → ZX (n + p) (m + q)
  | compose  {n m k : Nat} : ZX n m → ZX m k → ZX n k

/-- Sequential composition: `a ≫ b` feeds the outputs of `a` into the inputs of `b`. -/
scoped infixr:80 " ≫ " => ZX.compose -- type as \gg

/-- Parallel composition (stacking): `a ⊗ b` puts `a` and `b` side by side. -/
scoped infixr:70 " ⊗ " => ZX.stack

end SpLean.Algebraic
