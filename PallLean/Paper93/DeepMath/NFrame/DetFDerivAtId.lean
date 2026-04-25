import PallLean.Paper93.DeepMath.NFrame.DetDifferentiable
import PallLean.Paper93.DeepMath.NFrame.AdjugateOne

namespace PallLean.Paper93.DeepMath.NFrame

open scoped Matrix.Norms.Elementwise

/-- At A = I (identity), the Jacobi formula gives `fderiv det I (ΔA) = trace(ΔA)`. -/
theorem fderiv_det_at_one_exists {n : ℕ} :
    ∃ L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ,
      HasFDerivAt (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) L (1 : Matrix (Fin n) (Fin n) ℝ) :=
  ⟨fderiv ℝ Matrix.det 1, det_differentiable.differentiableAt.hasFDerivAt⟩

/-- `adjTraceAt I ΔA = trace(adj(I) · ΔA) = trace(I · ΔA) = trace(ΔA)`. -/
theorem adjTraceAt_at_one {n : ℕ} (ΔA : Matrix (Fin n) (Fin n) ℝ) :
    (1 : Matrix (Fin n) (Fin n) ℝ).adjugate * ΔA = ΔA := by
  rw [adjugate_one, Matrix.one_mul]

end PallLean.Paper93.DeepMath.NFrame
