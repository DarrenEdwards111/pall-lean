import Mathlib.LinearAlgebra.Matrix.PosDef

namespace PallLean.Paper93.DeepMath

/-- The sum of two positive semidefinite real matrices is positive semidefinite. -/
theorem psd_add {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A + B).PosSemidef :=
  hA.add hB

end PallLean.Paper93.DeepMath
