import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.NFrame

/-- Trace of identity matrix equals n (for Fin n). -/
theorem trace_one_eq_n {n : ℕ} :
    (1 : Matrix (Fin n) (Fin n) ℝ).trace = n := by
  rw [Matrix.trace_one]
  simp

/-- Trace of scalar identity: `(c • 1).trace = c · n`. -/
theorem trace_smul_one {n : ℕ} (c : ℝ) :
    (c • (1 : Matrix (Fin n) (Fin n) ℝ)).trace = c * n := by
  rw [Matrix.trace_smul, trace_one_eq_n]
  simp [smul_eq_mul]

end PallLean.Paper93.DeepMath.NFrame
