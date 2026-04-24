import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.LPS

/-- Adjacency matrix of complete graph on `Fin n`: `K i j = 1` if `i ≠ j`, else 0. -/
def completeAdj (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then 0 else 1

theorem completeAdj_symm (n : ℕ) : (completeAdj n).IsSymm := by
  ext i j
  by_cases h : i = j
  · subst h; rfl
  · simp [completeAdj, Matrix.transpose_apply, h, Ne.symm h]

end PallLean.Paper93.DeepMath.LPS
