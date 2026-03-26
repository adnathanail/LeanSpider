import LeanZX.All

open LeanZX

-- Quantum teleportation demo:
--   The proof holds for all phase values a, b ∈ {0, 1} (multiples of π)
abbrev teleportationStart (a b : Int) : ZXDiagram :=
  ZXDiagram.ofList
    [
      .input 0, .spider .Z ⟨0, 1⟩, .hadamard, .spider .X ⟨a, 1⟩,
      .spider .X ⟨0, 1⟩, .spider .X ⟨b, 1⟩,
      .spider .X ⟨b, 1⟩, .spider .Z ⟨a, 1⟩, .output 0
    ]
    [
      ⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 3⟩,
      ⟨1, 4⟩, ⟨4, 5⟩,
      ⟨4, 6⟩, ⟨6, 7⟩, ⟨7, 8⟩,
    ]
def teleportationEnd : ZXDiagram :=
  ZXDiagram.ofList
    [.input 0, .output 0]
    [⟨0, 1⟩]
-- Example of one of the 4 graphs (change the a and b values to see each possible graph)
#html (teleportationStart 1 1).toHtml
#html teleportationEnd.toHtml

-- Shared proof macro: the same set of rewrites is used to prove each case
local macro "zx_teleport" : tactic => `(tactic| (
  simp only [teleportationStart, ZXDiagram.ofList]
  zx_show; zx_cc 3; zx_hh 2 9; zx_sp 1 3
  zx_sp 4 5; zx_sp 4 6; zx_id 4; zx_sp 1 7; zx_id 1
  zx_rfl))

-- Proof that for every a,b ∈ {0, 1} teleportationStart a b ≈z teleportationEnd
theorem doTeleportationSimp : ∀ a b : Fin 2,
    teleportationStart ↑a.val ↑b.val ≈z teleportationEnd := by
  intro a b; match a, b with
  | ⟨0, _⟩, ⟨0, _⟩ => exact (by zx_teleport : teleportationStart 0 0 ≈z teleportationEnd)
  | ⟨0, _⟩, ⟨1, _⟩ => exact (by zx_teleport : teleportationStart 0 1 ≈z teleportationEnd)
  | ⟨1, _⟩, ⟨0, _⟩ => exact (by zx_teleport : teleportationStart 1 0 ≈z teleportationEnd)
  | ⟨1, _⟩, ⟨1, _⟩ => exact (by zx_teleport : teleportationStart 1 1 ≈z teleportationEnd)
-- Still only depends on the base axioms
#print axioms doTeleportationSimp
