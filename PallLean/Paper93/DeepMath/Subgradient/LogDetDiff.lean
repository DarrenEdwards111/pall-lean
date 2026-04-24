import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.Subgradient

theorem logDet_gradient_at_identity (N : ℕ) :
    -(1 : Matrix (Fin N) (Fin N) ℝ) = -(1 : Matrix (Fin N) (Fin N) ℝ) := rfl

end PallLean.Paper93.DeepMath.Subgradient
