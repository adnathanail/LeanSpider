import LeanZX.All

open LeanZX

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
-- Node indexes are 'stable' in that when nodes are removed from the graph, they are replaced with none
--   this means we don't have to update edges when nodes are removed from the graph
--   this also means that if we want to compare two graphs, we sometimes have to manually enter a bunch of nones
def zHadXSimplified : ZXDiagram :=
  { nodes := [some (.input 0), none, none, none, some (.output 0), none, some (.hadamard)]
    edges := [⟨0, 6⟩, ⟨4, 6⟩] }
-- Now we've defined two diagrams, you can view them in the InfoView:
--   Click the ∀ icon at the top right > Toggle InfoView
--   Then move your cursor to a line starting with #html
#html zHadX.toHtml
#html zHadXSimplified.toHtml

-- This is a proof that zHadX and zHadXSimplified are equivalent under the rules of the ZX calculus
--   If you click on each line, you'll see the current state of the graph
--     (The Tactic state may take up lots of room - you can fold it away by clicking the title)
--   zx_show just displays the current state of the graph
--   zx_rfl asserts that the goal state and the modified starting state are equal
theorem zHadXSimp : zHadX ≈z zHadXSimplified := by
  zx_show
  zx_cc 3
  zx_hh 2 5
  zx_sp 1 3
  zx_id 1
  zx_rfl
-- We can view which axioms were used for this proof, by putting the cursor on the line below
#print axioms zHadXSimp
-- You'll see 3 to do with equivalences of diagrams, 1 to do with equivalence of propositions, and 4 for the 4 ZX calculus rules used
-- This is a lot of axioms... we're working on it!

-- Example (Z ⊗ I)CNOT(Z ⊗ I): Z commutes with CNOT, and cancels with the second Z
#html zCnotZ.toHtml
#html cnot.toHtml
theorem dozCnotZ : zCnotZ ≈z cnot := by
  zx_show
  zx_sp 1 2
  zx_sp 1 3
  zx_rfl
#print axioms dozCnotZ

def piPiPiMinus : ZXDiagram :=
  ZXDiagram.ofList
    [.input 0, .spider .Z ⟨1, 1⟩, .spider .Z ⟨1, 1⟩, .spider .Z ⟨-1, 1⟩, .output 0]
    [⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩, ⟨3, 4⟩]
def pppmSimplified : ZXDiagram :=
  { nodes := [some (.input 0), some (.spider .Z ⟨1, 1⟩), none, none, some (.output 0)]
    edges := [⟨0, 1⟩, ⟨1, 4⟩] }
#html piPiPiMinus.toHtml
#html pppmSimplified.toHtml

-- Example: 3π ≣ π
theorem doPppmSimp : piPiPiMinus ≈z pppmSimplified := by
  zx_show
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
  { nodes := [some (.input 0), none, none, some (.output 0)]
    edges := [⟨0, 3⟩] }
#html piPiMinus.toHtml
#html ppmSimplified.toHtml

-- Example: Simplifying 2 pi phases to the identity
theorem doPpmSimp : piPiMinus ≈z ppmSimplified := by
  zx_show
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
#html exercise3point7.toHtml

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

-- Current challenge: Graph equality
--   Implemented some normalization - edges are always ordered, phases are always simplified
--   Another cheap win - strip out nones from the node list
--   Medium-term - graph ismorphism
