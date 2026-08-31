import SpLean.Algebraic.ZX
import SpLean.Algebraic.Equiv
import SpLean.Algebraic.Combinators
import SpLean.Algebraic.Tactics
import SpLean.Algebraic.Rules.Structural
import SpLean.Algebraic.Rules.HadamardHadamard

import SpLean.Panel

show_panel_widgets [local SpLean.ZXPanel]

namespace SpLean.Algebraic

/-- Colour change (arity 1 1): swap X spider for H Z H -/
theorem colour_change_X_Z_one_wire (α : AlgPhase) :
    ZX.spider .X 1 1 α ≈zx (ZX.hadamard ≫ ZX.spider .Z 1 1 α ≫ ZX.hadamard) := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, xSpiderSem]
  nth_rw 3 [Finset.univ_unique]
  rw [Finset.prod_singleton']
  simp only [Fin.isValue, Fin.default_eq_zero, Finset.univ_unique, Finset.prod_singleton]
  simp only [Finset.mul_sum, mul_assoc]

/-- Colour change (arity 1 1): swap Z spider for H X H -/
theorem colour_change_Z_X_one_wire (α : AlgPhase) :
    ZX.spider .Z 1 1 α ≈zx (ZX.hadamard ≫ ZX.spider .X 1 1 α ≫ ZX.hadamard) := by
  zx_rw [colour_change_X_Z_one_wire]
  zx_rw [← compose_assoc _ _ ZX.hadamard]
  zx_rw [← compose_assoc ZX.hadamard ZX.hadamard]
  zx_rw [hadamard_hadamard, wire_compose]
  zx_rw [compose_assoc]
  zx_rw [hadamard_hadamard]
  zx_rw [compose_wire]

/-- Colour change (arity n m): a Z spider with a Hadamard on every leg is an X spider. -/
theorem colour_change_X_Z (n m : ℕ) (α : AlgPhase) :
    ZX.spider .X n m α ≈zx (ZX.nHadamard n ≫ ZX.spider .Z n m α ≫ ZX.nHadamard m) := by
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  simp only [ZX.sem, xSpiderSem, nHadamard_sem]
  simp only [Finset.mul_sum, mul_assoc]

/-- Colour change state (arity 0 m): a Z spider state with a Hadamard on every output is an X spider state. -/
theorem colour_change_X_Z_state (m : ℕ) (α : AlgPhase) :
    ZX.spider .X 0 m α ≈zx (ZX.spider .Z 0 m α ≫ ZX.nHadamard m) := by
  zx_rw [colour_change_X_Z]
  rw [ZX.nHadamard]
  rw [ZX.nStack]
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  rw [ZX.sem]
  have hempty : ∀ g_1 : Wires 0, ZX.empty.sem f g_1 = 1 := by intro g_1 ; rw [ZX.sem]
  simp only [hempty, one_mul]
  rw [Finset.univ_unique, Finset.sum_singleton]
  congr
  exact List.ofFn_inj.mp rfl

/-- Colour change effect (arity n 0): a Z spider effect with a Hadamard on every input is an X spider effect. -/
theorem colour_change_X_Z_effect (n : ℕ) (α : AlgPhase) :
    ZX.spider .X n 0 α ≈zx (ZX.nHadamard n ≫ ZX.spider .Z n 0 α) := by
  zx_rw [colour_change_X_Z]
  nth_rw 2 [ZX.nHadamard]
  rw [ZX.nStack]
  zx_rw [← compose_assoc]
  refine ⟨1, one_ne_zero, fun f g => ?_⟩
  rw [one_mul]
  rw [ZX.sem]
  have hempty : ∀ g_1 : Wires 0, ZX.empty.sem g_1 g = 1 := by intro g_1 ; rw [ZX.sem]
  simp only [hempty, mul_one]
  exact Fintype.sum_subsingleton _ g

/-- Colour change (arity n m): an X spider with a Hadamard on every leg is a Z spider. -/
theorem colour_change_Z_X (n m : ℕ) (α : AlgPhase) :
    ZX.spider .Z n m α ≈zx (ZX.nHadamard n ≫ ZX.spider .X n m α ≫ ZX.nHadamard m) := by
  zx_rw [colour_change_X_Z]
  zx_rw [← compose_assoc _ _ (ZX.nHadamard m)]
  zx_rw [← compose_assoc (ZX.nHadamard _) (ZX.nHadamard _)]
  zx_rw [hadamard_hadamard_n]
  zx_rw [nWire_compose]
  zx_rw [compose_assoc]
  zx_rw [hadamard_hadamard_n]
  zx_rw [compose_nWire]

/-- Colour change state (arity 0 m): an X spider state with a Hadamard on every output is a Z spider state. -/
theorem colour_change_Z_X_state (m : ℕ) (α : AlgPhase) :
    ZX.spider .Z 0 m α ≈zx (ZX.spider .X 0 m α ≫ ZX.nHadamard m) := by
  zx_rw [colour_change_X_Z_state]
  zx_rw [compose_assoc]
  zx_rw [hadamard_hadamard_n]
  zx_rw [compose_nWire]

/-- Colour change effect (arity n 0): an Z spider effect with a Hadamard on every input is an Z spider effect. -/
theorem colour_change_Z_X_effect (n : ℕ) (α : AlgPhase) :
    ZX.spider .Z n 0 α ≈zx (ZX.nHadamard n ≫ ZX.spider .X n 0 α) := by
  zx_rw [colour_change_X_Z_effect]
  zx_rw [← compose_assoc]
  zx_rw [hadamard_hadamard_n]
  zx_rw [nWire_compose]

end SpLean.Algebraic
