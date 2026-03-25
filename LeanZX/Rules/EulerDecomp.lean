import LeanZX.Axioms
import LeanZX.Tactics

open Lean Elab Tactic Meta

/-- Euler decomposition of a Hadamard node into spiders.
    Variant 1: Z(π/2) — X(π/2) — Z(π/2)
    Variant 2: Z(-π/2) — X(-π/2) — Z(-π/2)
    Variant 3: Z(π/2) — X(0) — Z(π/2) with Z(-π/2) dangling off the X
    Variant 4: X(π/2) — Z(π/2) — X(π/2)
    Variant 5: X(-π/2) — Z(-π/2) — X(-π/2)
    Variant 6: X(π/2) — Z(0) — X(π/2) with X(-π/2) dangling off the Z -/
def ZXDiagram.eulerDecomp (d : ZXDiagram) (a : NodeId) (variant : Nat) : Except String ZXDiagram := do
  let nodeA ← (d.getNode? a).toExcept s!"Node {a} not found"
  unless nodeA.isHadamard do throw s!"Node {a} is not a Hadamard"
  let aNeighbors := d.neighbors a
  unless aNeighbors.length == 2 do throw s!"Node {a} must have exactly 2 neighbors"
  let left := aNeighbors[0]!
  let right := aNeighbors[1]!
  -- Remove the Hadamard
  let d := d.removeEdgesOf a
  let d := d.removeNode a
  match variant with
  | 1 =>
    -- Z(π/2) — X(π/2) — Z(π/2)
    let (d, ids) := d.addNodes [
      Node.spider .Z ⟨1, 2⟩,
      Node.spider .X ⟨1, 2⟩,
      Node.spider .Z ⟨1, 2⟩]
    let z1 := ids[0]!; let x1 := ids[1]!; let z2 := ids[2]!
    let d := d.addEdges [Edge.mk left z1, Edge.mk z1 x1, Edge.mk x1 z2, Edge.mk z2 right]
    return d
  | 2 =>
    -- Z(-π/2) — X(-π/2) — Z(-π/2)
    let (d, ids) := d.addNodes [
      Node.spider .Z ⟨-1, 2⟩,
      Node.spider .X ⟨-1, 2⟩,
      Node.spider .Z ⟨-1, 2⟩]
    let z1 := ids[0]!; let x1 := ids[1]!; let z2 := ids[2]!
    let d := d.addEdges [Edge.mk left z1, Edge.mk z1 x1, Edge.mk x1 z2, Edge.mk z2 right]
    return d
  | 3 =>
    -- Z(π/2) — X(0) — Z(π/2) with Z(-π/2) dangling off X(0)
    let (d, ids) := d.addNodes [
      Node.spider .Z ⟨1, 2⟩,
      Node.spider .X ⟨0, 1⟩,
      Node.spider .Z ⟨1, 2⟩,
      Node.spider .Z ⟨-1, 2⟩]
    let z1 := ids[0]!; let x1 := ids[1]!; let z2 := ids[2]!; let z3 := ids[3]!
    let d := d.addEdges [Edge.mk left z1, Edge.mk z1 x1, Edge.mk x1 z2, Edge.mk z2 right, Edge.mk x1 z3]
    return d
  | 4 =>
    -- X(π/2) — Z(π/2) — X(π/2)
    let (d, ids) := d.addNodes [
      Node.spider .X ⟨1, 2⟩,
      Node.spider .Z ⟨1, 2⟩,
      Node.spider .X ⟨1, 2⟩]
    let x1 := ids[0]!; let z1 := ids[1]!; let x2 := ids[2]!
    let d := d.addEdges [Edge.mk left x1, Edge.mk x1 z1, Edge.mk z1 x2, Edge.mk x2 right]
    return d
  | 5 =>
    -- X(-π/2) — Z(-π/2) — X(-π/2)
    let (d, ids) := d.addNodes [
      Node.spider .X ⟨-1, 2⟩,
      Node.spider .Z ⟨-1, 2⟩,
      Node.spider .X ⟨-1, 2⟩]
    let x1 := ids[0]!; let z1 := ids[1]!; let x2 := ids[2]!
    let d := d.addEdges [Edge.mk left x1, Edge.mk x1 z1, Edge.mk z1 x2, Edge.mk x2 right]
    return d
  | 6 =>
    -- X(π/2) — Z(0) — X(π/2) with X(-π/2) dangling off Z(0)
    let (d, ids) := d.addNodes [
      Node.spider .X ⟨1, 2⟩,
      Node.spider .Z ⟨0, 1⟩,
      Node.spider .X ⟨1, 2⟩,
      Node.spider .X ⟨-1, 2⟩]
    let x1 := ids[0]!; let z1 := ids[1]!; let x2 := ids[2]!; let x3 := ids[3]!
    let d := d.addEdges [Edge.mk left x1, Edge.mk x1 z1, Edge.mk z1 x2, Edge.mk x2 right, Edge.mk z1 x3]
    return d
  | _ => throw s!"Variant must be 1-6, got {variant}"

namespace LeanZX

axiom ZXDiagram.eulerDecomp_sound (d : ZXDiagram) (a : NodeId) (variant : Nat) (d' : ZXDiagram) :
  d.eulerDecomp a variant = .ok d' → d ≈z d'

/-- Euler decomposition of a Hadamard node into spiders.
    Usage: `zx_eu n v` where `n` is the Hadamard node ID and `v` is the variant (1-6). -/
syntax "zx_eu" num num : tactic

elab_rules : tactic
  | `(tactic| zx_eu $a $v) =>
    applyRewrite a "Euler Decomposition"
      ``ZXDiagram.eulerDecomp ``ZXDiagram.eulerDecomp_sound
      #[mkNatLit a.getNat, mkNatLit v.getNat]

end LeanZX
