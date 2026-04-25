import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.PathB

/-- For a 1×1 matrix A with A 0 0 = 1, the unique minor (det A) equals 1. -/
theorem fin_one_unit_minor (A : Matrix (Fin 1) (Fin 1) ℝ) (h : A 0 0 = 1) :
    A.det = 1 := by
  rw [Matrix.det_fin_one, h]

/-- For 1×1, det = A 0 0 (restated for clarity). -/
theorem fin_one_det_eq_entry (A : Matrix (Fin 1) (Fin 1) ℝ) :
    A.det = A 0 0 := Matrix.det_fin_one A

end PallLean.Paper93.DeepMath.PathB
