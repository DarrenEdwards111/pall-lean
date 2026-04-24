import Mathlib.LinearAlgebra.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.Amplituhedron

/-- Every positive definite real matrix is positive semidefinite. -/
theorem identity_minor_preserved {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (hM : M.PosDef) :
    M.PosSemidef :=
  hM.posSemidef

end PallLean.Paper93.DeepMath.Amplituhedron
