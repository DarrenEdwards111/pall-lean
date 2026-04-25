import PallLean.Paper93.DeepMath.NFrame.BarrierConvexHypothesis
import PallLean.Paper93.DeepMath.NFrame.EigenvectorUnitaryDet

namespace PallLean.Paper93.DeepMath.NFrame

open scoped Matrix

/-- Every Hermitian matrix has a spectral decomposition `A = Uᵀ D U` with U orthogonal
    (UᵀU = 1) and D diagonal. This wraps Mathlib's `IsHermitian.spectralTheorem`-type result
    plus our `hermitian_eigenvectorUnitary_det_sq` to show `(det U)² = 1`. -/
theorem isHermitian_has_spectral_decomposition {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, Uᵀ * U = 1 := by
  obtain ⟨U, _hU_eq, hU_sq⟩ := hermitian_eigenvectorUnitary_det_sq A hA
  exact ⟨U, hU_sq⟩

end PallLean.Paper93.DeepMath.NFrame
