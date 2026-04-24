import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

namespace PallLean.Paper93.DeepMath

theorem identity_posSemidef {N : ℕ} :
    (1 : Matrix (Fin N) (Fin N) ℝ).PosSemidef :=
  Matrix.PosSemidef.one

end PallLean.Paper93.DeepMath
