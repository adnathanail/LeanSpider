import ZxLean.ZXCalculus

namespace ZxLean

/-- Semantic equivalence of ZX diagrams (same linear map) -/
axiom ZXDiagram.equiv : ZXDiagram → ZXDiagram → Prop

scoped infix:50 " ≈z " => ZXDiagram.equiv

-- Equivalence relation properties
axiom ZXDiagram.equiv_refl (d : ZXDiagram) : d ≈z d
axiom ZXDiagram.equiv_symm {d₁ d₂ : ZXDiagram} : d₁ ≈z d₂ → d₂ ≈z d₁
axiom ZXDiagram.equiv_trans {d₁ d₂ d₃ : ZXDiagram} : d₁ ≈z d₂ → d₂ ≈z d₃ → d₁ ≈z d₃

-- ZX calculus axioms: rewrite rules preserve equivalence
axiom ZXDiagram.spiderFusion_sound (d : ZXDiagram) (a b : NodeId) (d' : ZXDiagram) :
  d.spiderFusion a b = some d' → d ≈z d'

axiom ZXDiagram.identityRemoval_sound (d : ZXDiagram) (a : NodeId) (d' : ZXDiagram) :
  d.identityRemoval a = some d' → d ≈z d'

end ZxLean
