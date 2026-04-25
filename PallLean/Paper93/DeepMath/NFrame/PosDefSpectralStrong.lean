import PallLean.Paper93.DeepMath.NFrame.EigenvectorUnitaryDet
import PallLean.Paper93.DeepMath.NFrame.PosDefTranspose

namespace PallLean.Paper93.DeepMath.NFrame

open scoped Matrix

/-- For any PosDef A, the eigenvector unitary U from Mathlib satisfies UᵀU = 1. -/
theorem posDef_eigenvectorUnitary_orthogonal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, Uᵀ * U = 1 := by
  obtain ⟨U, _, hU⟩ := hermitian_eigenvectorUnitary_det_sq A hA.1
  exact ⟨U, hU⟩

end PallLean.Paper93.DeepMath.NFrame
