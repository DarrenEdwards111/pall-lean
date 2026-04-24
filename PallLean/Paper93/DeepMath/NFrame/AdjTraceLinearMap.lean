import PallLean.Paper93.DeepMath.NFrame.AdjTraceBilinear

namespace PallLean.Paper93.DeepMath.NFrame

/-- `adjTraceAt A` packaged as a LinearMap. -/
noncomputable def adjTraceLinearMap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ where
  toFun := fun ΔA => adjTraceAt A ΔA
  map_add' := adjTraceAt_add A
  map_smul' := by
    intros c ΔA
    simp [adjTraceAt_smul, smul_eq_mul]

theorem adjTraceLinearMap_apply {n : ℕ} (A ΔA : Matrix (Fin n) (Fin n) ℝ) :
    adjTraceLinearMap A ΔA = adjTraceAt A ΔA := rfl

end PallLean.Paper93.DeepMath.NFrame
