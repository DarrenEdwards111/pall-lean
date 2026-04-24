import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

namespace PallLean.Paper93.DeepMath

/-- The rank of a matrix product is bounded above by the rank of the left factor. -/
theorem rank_mul_le_left_real {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ) :
    (A * B).rank ≤ A.rank :=
  Matrix.rank_mul_le_left A B

/-- The rank of a matrix product is bounded above by the rank of the right factor. -/
theorem rank_mul_le_right_real {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ) :
    (A * B).rank ≤ B.rank :=
  Matrix.rank_mul_le_right A B

end PallLean.Paper93.DeepMath
