import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

namespace PallLean.Paper93.DeepMath.GadgetRank

theorem identity_matrix_rank (k : ℕ) : (1 : Matrix (Fin k) (Fin k) ℝ).rank = k := by
  rw [Matrix.rank_one]
  exact Fintype.card_fin k

theorem zero_matrix_rank (k : ℕ) : (0 : Matrix (Fin k) (Fin k) ℝ).rank = 0 := by
  simp [Matrix.rank]
