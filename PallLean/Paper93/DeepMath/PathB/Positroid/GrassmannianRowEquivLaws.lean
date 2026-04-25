import PallLean.Paper93.DeepMath.PathB.Positroid.GrassmannianRowSpan

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The trivial row equivalence relation is reflexive. -/
theorem trivialRowEquiv_refl_general {k n : ℕ} (M : Matrix (Fin k) (Fin n) ℝ) :
    trivialRowEquiv M M := rfl

/-- The trivial row equivalence relation is symmetric. -/
theorem trivialRowEquiv_symm_general {k n : ℕ} {M N : Matrix (Fin k) (Fin n) ℝ} :
    trivialRowEquiv M N → trivialRowEquiv N M :=
  fun h => h.symm

/-- The trivial row equivalence relation is transitive. -/
theorem trivialRowEquiv_trans_general {k n : ℕ} {M N P : Matrix (Fin k) (Fin n) ℝ} :
    trivialRowEquiv M N → trivialRowEquiv N P → trivialRowEquiv M P :=
  fun h₁ h₂ => h₁.trans h₂

/-- The trivial row equivalence relation is an equivalence relation
    (reflexive + symmetric + transitive). -/
theorem trivialRowEquiv_is_equivalence (k n : ℕ) :
    Equivalence (@trivialRowEquiv k n) :=
  ⟨@trivialRowEquiv_refl_general k n,
   @trivialRowEquiv_symm_general k n,
   @trivialRowEquiv_trans_general k n⟩

/-- The GL row equivalence is reflexive (witness = identity). -/
theorem glRowEquiv_refl_general {k n : ℕ} (M : Matrix (Fin k) (Fin n) ℝ) :
    glRowEquiv M M := glRowEquiv_refl M

end PallLean.Paper93.DeepMath.PathB.Positroid
