import LeanZX.ZXDiagram

namespace LeanZX

/-- Equivalence of ZX diagrams: equal after compaction and normalization -/
def ZXDiagram.equiv (d₁ d₂ : ZXDiagram) : Prop :=
  d₁.compact.normalize = d₂.compact.normalize

scoped infix:50 " ≈z " => ZXDiagram.equiv

instance (d₁ d₂ : ZXDiagram) : Decidable (d₁ ≈z d₂) :=
  inferInstanceAs (Decidable (d₁.compact.normalize = d₂.compact.normalize))

-- Equivalence relation properties (all provable now, no axioms needed)
theorem ZXDiagram.equiv_refl (d : ZXDiagram) : d ≈z d :=
  rfl

theorem ZXDiagram.equiv_symm {d₁ d₂ : ZXDiagram} : d₁ ≈z d₂ → d₂ ≈z d₁ :=
  Eq.symm

theorem ZXDiagram.equiv_trans {d₁ d₂ d₃ : ZXDiagram} : d₁ ≈z d₂ → d₂ ≈z d₃ → d₁ ≈z d₃ :=
  Eq.trans

end LeanZX
