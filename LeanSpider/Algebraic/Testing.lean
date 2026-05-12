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

/-! ## `zx_alg_fusion` — graph-style spider fusion tactic

    Apply Z-spider fusion at two named node IDs. The IDs match those
    assigned by `ZX.toPositionedDiagram`, so they are the same numbers
    you see in the rendered diagram.

    Scope: direct-compose only. Both spiders must be Z, with arities
    `(_, 1)` and `(1, _)`, and sit as the immediate children of a single
    `compose`. The fused result has the *raw* phase sum (no
    simplification) — phase simplification stays a separate concern. -/

-- (1) Top-level fusion with concrete phases. IDs: s1=0, s2=1.
--     The tactic gcd-reduces the summed phase, so ⟨1,4⟩+⟨1,4⟩ = ⟨8,16⟩
--     becomes ⟨1,2⟩.
theorem zxAlgFusion_topLevel :
    (ZX.spider .Z 1 1 ⟨1, 4⟩ × ZX.spider .Z 1 1 ⟨1, 4⟩)
      ≃ZX ZX.spider .Z 1 1 ⟨1, 2⟩ := by
  zx_alg_fusion 0 1
  rfl

theorem zxAlgFusion_parameterized (α β : Phase) :
    (ZX.spider .Z 1 1 α × ZX.spider .Z 1 1 β)
      ≃ZX ZX.spider .Z 1 1 (α + β) := by
  zx_alg_fusion 0 1
  rfl

theorem zxAlgFusion_parameterized2 (α : Phase) :
    (ZX.spider .Z 1 1 α × ZX.spider .Z 1 1 ⟨1, 2⟩)
      ≃ZX ZX.spider .Z 1 1 (α + ⟨1, 2⟩) := by
  zx_alg_fusion 0 1
  rfl

def zaf_pa3a (α : Phase) : ZX 1 1 := (ZX.spider .Z 1 1 α × ZX.spider .Z 1 1 (-α))
theorem zxAlgFusion_parameterized3a (α : Phase) :
    zaf_pa3a α
      ≃ZX ZX.spider .Z 1 1 := by
  zx_alg_fusion 0 1
  exact spider_phase_eq (congr_phase (by
    show (Phase.add α (Phase.neg α)).num * _ = _
    unfold Phase.add Phase.neg
    simp))

def zaf_pa3b (α : Phase) : ZX 1 1 := zaf_pa3a α × ZX.spider .Z 1 1 ⟨1, 2⟩
theorem zxAlgFusion_parameterized3b (α : Phase) :
    zaf_pa3b α
      ≃ZX (ZX.spider .Z 1 1 × ZX.spider .Z 1 1 ⟨1, 2⟩) := by
  zx_alg_fusion 0 1
  exact ZX.compose_congr
    (spider_phase_eq (congr_phase (by
      show (Phase.add α (Phase.neg α)).num * _ = _
      unfold Phase.add Phase.neg
      simp)))
    (ZX.equiv_refl _)

-- (2) Nested under a surrounding compose. IDs (DFS):
--   s1=0 (outer left), s2=1 (target left), s3=2 (target right), s4=3 (outer right).
theorem zxAlgFusion_nested :
    ZX.compose
        (ZX.compose (ZX.spider .Z 1 1 ⟨1, 8⟩)
          (ZX.compose (ZX.spider .Z 1 1 ⟨1, 4⟩) (ZX.spider .Z 1 1 ⟨1, 4⟩)))
        (ZX.spider .Z 1 1 ⟨1, 8⟩)
      ≃ZX
    ZX.compose
        (ZX.spider .Z 1 1 (⟨5, 8⟩))
        (ZX.spider .Z 1 1 ⟨1, 8⟩) := by
  zx_alg_fusion 1 2
  zx_alg_fusion 0 1
  rfl

-- Axiom audit: proofs built by the tactic depend only on the standard
-- three axioms — no project-local soundness axioms.
#print axioms zxAlgFusion_topLevel
#print axioms zxAlgFusion_parameterized
#print axioms zxAlgFusion_nested
