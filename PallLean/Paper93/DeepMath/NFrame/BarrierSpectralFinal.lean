import PallLean.Paper93.DeepMath.NFrame.BarrierConvexFromSpectral
import PallLean.Paper93.DeepMath.NFrame.PosDefSpectralStrong

namespace PallLean.Paper93.DeepMath.NFrame

open scoped Matrix

/-- Final spectral fact: every PosDef matrix has an orthogonal U with UᵀU = 1. -/
theorem posDef_has_orthogonal_eigenvector_basis {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, Uᵀ * U = 1 :=
  posDef_eigenvectorUnitary_orthogonal A hA

end PallLean.Paper93.DeepMath.NFrame
