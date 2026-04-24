import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.RealPiStar

theorem realPiStar_identity_rank {N : ℕ} :
    (1 : Matrix (Fin N) (Fin N) ℝ).rank = N := by
  rw [Matrix.rank_one]
  exact Fintype.card_fin N

end PallLean.Paper93.DeepMath.RealPiStar
