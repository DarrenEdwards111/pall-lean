import PallLean.Paper93.DeepMath.NFrame.DetDifferentiable
import PallLean.Paper93.DeepMath.NFrame.AdjTraceBilinear

namespace PallLean.Paper93.DeepMath.NFrame

open scoped Matrix.Norms.Elementwise

/-- For any n, `Matrix.det` has Fréchet derivative at every A. The candidate Jacobi
    formula `fderiv det A = adjTraceLinearMap A` is proved at n=1 and n=2 separately;
    the general-n identification awaits a cofactor-expansion induction. -/
theorem det_fderiv_exists_general {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ,
      HasFDerivAt (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) L A :=
  ⟨fderiv ℝ Matrix.det A, det_differentiable.differentiableAt.hasFDerivAt⟩

/-- The candidate adjTrace linear map is well-defined for general n. -/
theorem adjTraceAt_well_defined_general {n : ℕ} (A ΔA : Matrix (Fin n) (Fin n) ℝ) :
    ∃ r : ℝ, adjTraceAt A ΔA = r :=
  ⟨adjTraceAt A ΔA, rfl⟩

end PallLean.Paper93.DeepMath.NFrame
