import SpLean.Hypergraph.Decide

/-!
# Searching for an isomorphism

The certificate `Iso.ofTables` wants is plain numbers, and *finding* it is
ordinary combinatorial search — so it is written here as ordinary computable
Lean, not as meta code. Nothing in this file is trusted: a wrong or missing
answer costs a failed tactic, never an unsound proof, because the tables it
returns are checked by `decide` at the point of use.

The search works up to `Hyp.rep`, i.e. on *classes* of wires rather than
wires, since that is the level an isomorphism is stated at. It matches boxes to
boxes and legs to legs by backtracking, propagating the class correspondence
each match forces, and seeds it with the boundary — which is not a choice, so
it prunes the search before it starts.
-/

namespace SpLean.Hypergraph

/-- A box, flattened: a key that decides when two boxes may be matched, and the
wire classes on its legs. -/
structure BoxData where
  key : ℕ × Int × ℕ
  legs : List ℕ
  deriving Repr, DecidableEq, Inhabited

/-- A hypergraph, flattened, with every wire already replaced by its class. -/
structure HypData where
  wires : ℕ
  reps : List ℕ
  boxes : List BoxData
  ids : List (ℕ × ℕ)
  inputs : List ℕ
  outputs : List ℕ
  deriving Repr, Inhabited

/-- The tables `Iso.ofTables` takes. -/
structure Tables where
  w : List ℕ
  wInv : List ℕ
  bp : List ℕ
  bpInv : List ℕ
  lp : List (List ℕ)
  lpInv : List (List ℕ)
  deriving Repr, Inhabited

namespace Search

/-- A partial correspondence between the two hypergraphs' wire classes. -/
abbrev Map := List (ℕ × ℕ)

/-- Extend the correspondence with `a ↦ b`, failing if either side is already
spoken for by a different partner. -/
def assign (m : Map) (a b : ℕ) : Option Map :=
  match m.find? (fun p => p.1 = a), m.find? (fun p => p.2 = b) with
  | some p, _ => if p.2 = b then some m else none
  | none, some _ => none
  | none, none => some ((a, b) :: m)

def assignAll (m : Map) : List (ℕ × ℕ) → Option Map
  | [] => some m
  | (a, b) :: rest => do assignAll (← assign m a b) rest

/-- Match the remaining boxes of the first hypergraph against the unused boxes
of the second, recording for each the leg permutation used. -/
def matchBoxes (A B : HypData) :
    List ℕ → List ℕ → Map → List (ℕ × ℕ × List ℕ) → Option (Map × List (ℕ × ℕ × List ℕ))
  | [], _, m, acc => some (m, acc)
  | i :: rest, avail, m, acc =>
      let bi := A.boxes.getD i default
      avail.firstM fun j =>
        let bj := B.boxes.getD j default
        if bi.key ≠ bj.key ∨ bi.legs.length ≠ bj.legs.length then none
        else
          (List.permutations (List.range bj.legs.length)).firstM fun σ => do
            -- leg `k` of `bi` is matched with leg `σ[k]` of `bj`
            let pairs := (List.range bi.legs.length).map fun k =>
              (bi.legs.getD k 0, bj.legs.getD (σ.getD k 0) 0)
            let m ← assignAll m pairs
            matchBoxes A B rest (avail.filter (· ≠ j)) m ((i, j, σ) :: acc)

/-- Pair up whatever classes the boxes and boundary did not reach. -/
def completeMap (A B : HypData) (m : Map) : Map :=
  let usedA := m.map Prod.fst
  let usedB := m.map Prod.snd
  let freeA := A.reps.dedup.filter (· ∉ usedA)
  let freeB := B.reps.dedup.filter (· ∉ usedB)
  m ++ (freeA.zip freeB)

/-- Invert a table given as a list, over a domain of size `n`. -/
def invertTable (t : List ℕ) (n : ℕ) : List ℕ :=
  (List.range n).map fun j => (List.range t.length).find? (fun i => t.getD i 0 = j) |>.getD 0

/-- Find tables witnessing an isomorphism, or fail. -/
def findTables (A B : HypData) : Option Tables := do
  guard (A.boxes.length = B.boxes.length)
  guard (A.inputs.length = B.inputs.length)
  guard (A.outputs.length = B.outputs.length)
  -- The boundary is forced: input `i` goes to input `i`, and likewise outputs.
  let seed := (A.inputs.zip B.inputs ++ A.outputs.zip B.outputs).map fun p =>
    (A.reps.getD p.1 0, B.reps.getD p.2 0)
  let m₀ ← assignAll [] seed
  let (m, boxMatches) ←
    matchBoxes A B (List.range A.boxes.length) (List.range B.boxes.length) m₀ []
  let m := completeMap A B m
  let cls (a : ℕ) : ℕ := (m.find? (fun p => p.1 = a)).map Prod.snd |>.getD 0
  let clsInv (b : ℕ) : ℕ := (m.find? (fun p => p.2 = b)).map Prod.fst |>.getD 0
  let w := (List.range A.wires).map fun v => cls (A.reps.getD v 0)
  let wInv := (List.range B.wires).map fun v => clsInv (B.reps.getD v 0)
  let bp := (List.range A.boxes.length).map fun i =>
    (boxMatches.find? (fun t => t.1 = i)).map (fun t => t.2.1) |>.getD 0
  let lp := (List.range A.boxes.length).map fun i =>
    (boxMatches.find? (fun t => t.1 = i)).map (fun t => t.2.2) |>.getD []
  pure { w, wInv, bp, bpInv := invertTable bp B.boxes.length,
         lp, lpInv := lp.map fun σ => invertTable σ σ.length }

end Search

/-- Flatten a hypergraph for the search. -/
def Hyp.data {Φ : Type} {n m : ℕ} (key : Label Φ → ℕ × Int × ℕ) (H : Hyp Φ n m) : HypData where
  wires := H.wires
  reps := (List.finRange H.wires).map fun v => (H.rep v).val
  boxes := (List.finRange H.boxCount).map fun i =>
    { key := key (H.boxes i).label
      legs := (List.finRange (H.boxes i).arity).map fun k =>
        (H.rep ((H.boxes i).legs k)).val }
  ids := (List.finRange H.idCount).map fun k => ((H.ids k).1.val, (H.ids k).2.val)
  inputs := (List.finRange n).map fun i => (H.inputs i).val
  outputs := (List.finRange m).map fun j => (H.outputs j).val

end SpLean.Hypergraph
