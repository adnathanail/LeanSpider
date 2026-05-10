import LeanSpider.All

open LeanSpider.Algebraic

-- Spider fusion only depends on `propext`, `Classical.choice`, `Quot.sound`
--   the standard Mathlib three, no project-local axioms.
#print axioms LeanSpider.Algebraic.Z_spiderFusion

-- Algebraic-ZX terms can be rendered
open LeanSpider.Algebraic
def algSpider : ZX 1 1 := .spider .Z 1 1 ⟨1, 2⟩
#html algSpider.toHtml

-- Example spider fusion proof
abbrev algFusionLHS : ZX 1 1 := .spider .Z 1 1 ⟨1, 4⟩ × .spider .Z 1 1 ⟨1, 4⟩
#html algFusionLHS.toHtml

abbrev algFusionRHS : ZX 1 1 := .spider .Z 1 1 ⟨1, 2⟩
#html algFusionRHS.toHtml

theorem algFusion : algFusionLHS ≃ZX algFusionRHS := by
  show _ = _
  rw [Z_spiderFusion]
  exact spider_phase_eq (congr_phase (by decide))

def algLayoutTest1 : ZX 4 4 := GateCNOT ⊗ GateCNOT
#html algLayoutTest1.toHtml

def algLayoutTest2 : ZX 2 2 := GateCNOT × GateCNOT
#html algLayoutTest2.toHtml

def algLayoutTest3 : ZX 3 3 := (GateCNOT ⊗ .wire) × (.wire ⊗ GateCNOT)
#html algLayoutTest3.toHtml

def algLayoutTest4a : ZX 2 4 := (.spider .Z 1 3 ⊗ .wire)
def algLayoutTest4b : ZX 4 2 := (.wire ⊗ .spider .Z 3 1)
def algLayoutTest4 : ZX 2 2 := (.spider .Z 1 3 ⊗ .wire) × (.wire ⊗ .spider .X 3 1)
#html algLayoutTest4.toHtml

def algExercise3point7a : ZX 2 3 :=
  (.wire ⊗ .wire ⊗ .spider .Z 0 1) ×
  (.wire ⊗ GateNOTC)
def algExercise3point7b : ZX 3 3 := .wire ⊗ .hadamard ⊗ .spider .X 1 1 ⟨1, 1⟩
def algExercise3point7c : ZX 3 2 := (GateNOTC ⊗ .spider .X 1 0)
def algExercise3point7d : ZX 2 2 := (.wire ⊗ .hadamard) × GateCX
def algExercise3point7 : ZX 2 2 := ((algExercise3point7a × algExercise3point7b) × algExercise3point7c) × algExercise3point7d
#html algExercise3point7.toHtml
