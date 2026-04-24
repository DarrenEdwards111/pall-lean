import PallLean.Paper93.DeepMath.NFrame.DetFinTwoGrad

namespace PallLean.Paper93.DeepMath.NFrame

/-- For 2×2 matrices, `det` has Fréchet derivative at A (existence only — explicit
    identification as ΔA ↦ A 1 1 · ΔA 0 0 - A 0 1 · ΔA 1 0 - A 1 0 · ΔA 0 1 + A 0 0 · ΔA 1 1
    is the Jacobi formula at n=2 but we just assert existence here). -/
theorem det_fin_two_hasFDerivAt_exists (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ (L : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℝ),
      HasFDerivAt (Matrix.det : Matrix (Fin 2) (Fin 2) ℝ → ℝ) L A :=
  ⟨fderiv ℝ Matrix.det A,
    det_fin_two_differentiable.differentiableAt.hasFDerivAt⟩

end PallLean.Paper93.DeepMath.NFrame
