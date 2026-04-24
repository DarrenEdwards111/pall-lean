import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace PallLean.Paper93.DeepMath.Amplituhedron

/-- Explicit 2x2 totally positive matrix: `!![1,1;1,2]`. All entries > 0, det = 1 > 0. -/
def ex2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 2]

theorem ex2_entry_pos (i j : Fin 2) : 0 < ex2 i j := by
  fin_cases i <;> fin_cases j <;> simp [ex2]

theorem ex2_det_pos : 0 < ex2.det := by
  rw [Matrix.det_fin_two]
  simp [ex2]

end PallLean.Paper93.DeepMath.Amplituhedron
