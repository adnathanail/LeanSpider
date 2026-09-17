import SpLean.All

open SpLean
-- zCnotZ and cnot below come from SpLean/Axiomatic/Examples.lean
open SpLean.Examples

-- Show the current diagram in a panel alongside the tactic state
show_panel_widgets [local ZXPanel]

-- Abbreviate deep subterms in the Tactic state as `⋯`, so the goal stays short.
-- Hover a `⋯` to see what it stands for. Lower the threshold to elide more.
set_option pp.deepTerms false
set_option pp.deepTerms.threshold 1

def main : IO Unit :=
  IO.println "Open Main.lean in VS Code to see the ZX diagram in the InfoView."

-- This is how we define a diagram
def zHadX : ZXDiagram :=
  ZXDiagram.ofList
    -- We give a list of node types:
    --   inputs and outputs have a unique identifier
    --   Z and X spiders have a phase, expressed as a fractional multiple of pi
    [.input 0, .spider .Z ⟨1, 1⟩, .hadamard, .spider .X ⟨1, 1⟩, .output 0]
    -- We then give a list of edges, where the nodes are identified by their index in the list
    [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩]
def zHadXSimplified : ZXDiagram :=
  ZXDiagram.ofList
    [.input 0, .output 0, .hadamard]
    [⟨0, 2⟩, ⟨1, 2⟩]
-- Now we've defined two diagrams, you can view them in the InfoView:
--   Click the ∀ icon at the top right > Toggle InfoView
--   Then move your cursor to a line starting with #zx
#zx zHadX
#zx zHadXSimplified

-- This is a proof that zHadX and zHadXSimplified are equivalent under the rules of the ZX calculus
--   If you click on each line, you'll see the current state of the graph in the ZXPanel
--     (The Tactic state may take up lots of room - you can fold it away by clicking the title)
--   zx_rfl asserts that the goal state and the modified starting state are equal
theorem zHadXSimp : zHadX ≈z zHadXSimplified := by
  zx_cc 3
  zx_hh 2 5
  zx_sp 1 3
  zx_id 1
  zx_rfl
-- We can view which axioms were used for this proof, by putting the cursor on the line below
#print axioms zHadXSimp
-- You'll see 2 of Lean's own foundational axioms (propext and Quot.sound, pulled in by
--   the decidability machinery behind zx_rfl), and 4 for the 4 ZX calculus rules used
-- The 4 rule axioms are the ones we owe a proof of... we're working on it!

-- Example (Z ⊗ I)CNOT(Z ⊗ I): Z commutes with CNOT, and cancels with the second Z
#zx zCnotZ
#zx cnot
theorem dozCnotZ : zCnotZ ≈z cnot := by
  zx_sp 1 2
  zx_sp 1 3
  -- If you need to see the raw json, you can use the zx_debug tactic
  zx_debug
  zx_rfl
#print axioms dozCnotZ

def piPiPiMinus : ZXDiagram :=
  ZXDiagram.ofList
    [.input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨1, 1⟩, .spider .Z ⟨-1, 1⟩, .output 0]
    [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩]
def pppmSimplified : ZXDiagram :=
  ZXDiagram.ofList
    [.input 0, .spider .Z ⟨1, 1⟩, .output 0]
    [⟨0, 1⟩, ⟨1, 2⟩]
#zx piPiPiMinus
#zx pppmSimplified

-- Example: 3π ≣ π
theorem doPppmSimp : piPiPiMinus ≈z pppmSimplified := by
  -- Using Lean machinery to help us
  --   the repeat tactic is built into lean, and repeatedly applies another tactic until it can't any more
  --   here we are using zx_sp with just 1 argument, which searches for any available neighbouring spider to fuse with
  repeat zx_sp 1
  zx_rfl
#print axioms doPppmSimp

def piPiMinus : ZXDiagram :=
  ZXDiagram.ofList
    [.input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨1, 1⟩, .output 0]
    [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩]
def ppmSimplified : ZXDiagram :=
  ZXDiagram.ofList
    [.input 0, .output 0]
    [⟨0, 1⟩]
#zx piPiMinus
#zx ppmSimplified

-- Example: Simplifying 2 pi phases to the identity
theorem doPpmSimp : piPiMinus ≈z ppmSimplified := by
  -- Using a derived rule:
  --   we can combine our axiomatic rewrites into more complex ones
  --   If you hold 'command' and click on the zx_pipi on the line below, you'll see its definition
  --   It consists of zx_sp and zx_id
  zx_pipi 1
  zx_rfl
-- If we check our axioms, we'll see only the equivalence ones, and spider fusion and identity removal
#print axioms doPpmSimp
-- So the size of the set of axioms won't get larger, as we implement more derived rules!

def exercise3point7 : ZXDiagram :=
  ZXDiagram.ofList
    [
      .input 0, .spider .X ⟨0, 1⟩, .spider .Z ⟨0, 1⟩, .output 0,
      .hadamard,
      .input 1, .spider .X ⟨0, 1⟩, .hadamard, .spider .Z ⟨0, 1⟩, .hadamard, .spider .Z ⟨0, 1⟩, .output 1,
      .spider .Z ⟨0, 1⟩, .spider .Z ⟨0, 1⟩, .spider .X ⟨1, 1⟩, .spider .X ⟨0, 1⟩,
    ]
    [
      ⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩,
      ⟨4, 2⟩,
      ⟨5, 6⟩, ⟨6, 7⟩, ⟨7, 8⟩, ⟨8, 1⟩, ⟨8, 9⟩, ⟨9, 10⟩, ⟨10, 4⟩, ⟨10, 11⟩,
      ⟨12, 13⟩, ⟨13, 6⟩, ⟨13, 14⟩, ⟨14, 15⟩,
    ]
#zx exercise3point7

-- A larger example (Exercise 3.7 - Picturing Quantum Systems)
-- Current challenge: Rendering - with just the graph representation, the code has to guess how is best to lay out the diagram
example : ∃ d', exercise3point7 ≈z d' := by
  zx_explore
  zx_sp 12 13
  zx_sp 14 15
  zx_id 12
  zx_sp 14 6
  zx_cc 8
  zx_hh 7 16
  zx_hh 9 18
  zx_sp 14 8
  zx_unsp 14 ⟨0, 1⟩ ⟨1, 1⟩ [10]
  zx_pi 19 10
  zx_cc 20
  zx_hh 4 22
  zx_sp 20 2
  zx_unsp 20 ⟨0, 1⟩ ⟨1, 1⟩ [3]
  zx_rfl

-- Algebraic-ZX terms can now be rendered too: `#zx` draws them in the same
-- widget shown above.
open SpLean.Algebraic
def algSpider : ZX 1 1 := .spider .Z 1 1 (π/2)
#zx algSpider

def algFusionLHS : ZX 1 1 := .spider .Z 1 1 (π/4) ≫ .spider .Z 1 1 (π/4)
#zx algFusionLHS

def algStack : ZX 2 2 := .wire ⊗ .hadamard
#zx algStack

def algCnot : ZX 2 2 := (.spider .Z 1 2 ⊗ .wire) ≫ (.wire ⊗ .spider .X 2 1)
#zx algCnot

def algNotc : ZX 2 2 := (.spider .X 1 2 ⊗ .wire) ≫ (.wire ⊗ .spider .Z 2 1)
#zx algNotc

def algCx : ZX 2 2 :=
  (
    (.spider .Z 1 2 ⊗ .wire) ≫
    -- Ascribed because `⊗` is right-associative:
    --   the arity of the right-hand stack is `1 + (1 + 1)`,
    --   which the unifier will not match against the
    --   `2 + 1` it gets from the left-hand side of the `≫`.
    (.wire ⊗ .hadamard ⊗ .wire : ZX 3 3)
  ) ≫
  (.wire ⊗ .spider .Z 2 1)
#zx algCx

def algLayoutTest1 : ZX 4 4 := algCnot ⊗ algCnot
#zx algLayoutTest1

def algLayoutTest2 : ZX 2 2 := algCnot ≫ algCnot
#zx algLayoutTest2

def algLayoutTest3 : ZX 3 3 := (algCnot ⊗ .wire) ≫ (.wire ⊗ algCnot)
#zx algLayoutTest3

def algLayoutTest4a : ZX 2 4 := (.spider .Z 1 3 ⊗ .wire)
def algLayoutTest4b : ZX 4 2 := (.wire ⊗ .spider .Z 3 1)
def algLayoutTest4 : ZX 2 2 := (.spider .Z 1 3 ⊗ .wire) ≫ (.wire ⊗ .spider .X 3 1)
#zx algLayoutTest4

def algExercise3point7a : ZX 2 3 :=
  (.wire ⊗ .wire ⊗ .spider .Z 0 1) ≫
  (.wire ⊗ algNotc)
def algExercise3point7b : ZX 3 3 := .wire ⊗ .hadamard ⊗ .spider .X 1 1 π
def algExercise3point7c : ZX 3 2 := (algNotc ⊗ .spider .X 1 0)
def algExercise3point7d : ZX 2 2 := (.wire ⊗ .hadamard) ≫ algCx
def algExercise3point7 : ZX 2 2 := ((algExercise3point7a ≫ algExercise3point7b) ≫ algExercise3point7c) ≫ algExercise3point7d
#zx algExercise3point7

def swapTest : ZX 2 2 := (.spider .Z 1 1 ⊗ .spider .Z 1 1) ≫ .swap
#zx swapTest

def swapTest2 : ZX 2 2 := (.spider .Z 1 1 ⊗ .spider .Z 1 1) ≫ .swap ≫ (.spider .Z 1 1 ⊗ .spider .Z 1 1)
#zx swapTest2
