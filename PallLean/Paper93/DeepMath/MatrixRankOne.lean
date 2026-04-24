import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

namespace PallLean.Paper93.DeepMath

theorem identity_rank_N (N : ℕ) : (1 : Matrix (Fin N) (Fin N) ℝ).rank = N := by
  rw [Matrix.rank_one]; exact Fintype.card_fin N
