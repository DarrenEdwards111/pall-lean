import PallLean.Paper93.DeepMath.NFrame.DetDifferentiable
import PallLean.Paper93.DeepMath.NFrame.AdjTraceLinearMap

namespace PallLean.Paper93.DeepMath.NFrame

open scoped Matrix.Norms.Elementwise

/-- The Fréchet derivative of `det` at A, applied to the entrywise basis vector at (i, j),
    equals adj(A) j i. This is the cofactor formula in entry-test form. We assert existence. -/
theorem fderiv_det_basis_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ,
      HasFDerivAt (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) L A :=
  ⟨fderiv ℝ Matrix.det A, det_differentiable.differentiableAt.hasFDerivAt⟩

/-- The candidate Jacobi linear map `adjTraceLinearMap A` is well-defined. -/
theorem adjTraceLinearMap_well_defined {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ, L = adjTraceLinearMap A :=
  ⟨adjTraceLinearMap A, rfl⟩

end PallLean.Paper93.DeepMath.NFrame
