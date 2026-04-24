import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.RealPiStar

theorem realPiStar_identity_idempotent {N : ℕ} :
    (1 : Matrix (Fin N) (Fin N) ℝ) * 1 = 1 := by simp

end PallLean.Paper93.DeepMath.RealPiStar
