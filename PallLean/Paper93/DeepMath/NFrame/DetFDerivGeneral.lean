import PallLean.Paper93.DeepMath.NFrame.DetDifferentiable
import PallLean.Paper93.DeepMath.NFrame.AdjTraceLinearMap

namespace PallLean.Paper93.DeepMath.NFrame

open scoped Matrix.Norms.Elementwise

/-- For every n and every A, there exists a continuous linear map L such that
    `HasFDerivAt Matrix.det L A`. (Existence form; the explicit identification
    `L = adjTraceLinearMap A` is the Jacobi formula and requires further composition.) -/
theorem det_hasFDerivAt_exists {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ,
      HasFDerivAt (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) L A :=
  ⟨fderiv ℝ Matrix.det A, det_differentiable.differentiableAt.hasFDerivAt⟩

/-- The fderiv of det at A is a continuous linear map. (Trivially, by Fréchet differentiability.) -/
theorem fderiv_det_isCLM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ,
      L = fderiv ℝ Matrix.det A :=
  ⟨fderiv ℝ Matrix.det A, rfl⟩

end PallLean.Paper93.DeepMath.NFrame
