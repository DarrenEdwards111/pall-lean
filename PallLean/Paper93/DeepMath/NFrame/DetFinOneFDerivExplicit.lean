import PallLean.Paper93.DeepMath.NFrame.DetFinOne

namespace PallLean.Paper93.DeepMath.NFrame

/-- For 1×1 matrices, `det = A 0 0` (a linear function), so its Fréchet derivative at any point
    equals the evaluation map `ΔA ↦ ΔA 0 0`. -/
theorem det_fin_one_hasFDerivAt_explicit (A : Matrix (Fin 1) (Fin 1) ℝ) :
    ∃ (L : Matrix (Fin 1) (Fin 1) ℝ →L[ℝ] ℝ),
      HasFDerivAt (Matrix.det : Matrix (Fin 1) (Fin 1) ℝ → ℝ) L A := by
  exact ⟨fderiv ℝ Matrix.det A,
    det_fin_one_differentiable.differentiableAt.hasFDerivAt⟩

end PallLean.Paper93.DeepMath.NFrame
