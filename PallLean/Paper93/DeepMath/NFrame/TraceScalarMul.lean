import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.NFrame

/-- Trace of c • I = c · n. -/
theorem trace_smul_one_eq {n : ℕ} (c : ℝ) :
    (c • (1 : Matrix (Fin n) (Fin n) ℝ)).trace = c * n := by
  rw [Matrix.trace_smul, Matrix.trace_one]
  simp

/-- Jacobi identity `A · adj A = det A · I` transposed: trace form. -/
theorem trace_A_mul_adjugate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (A * A.adjugate).trace = A.det * n := by
  rw [Matrix.mul_adjugate]
  exact trace_smul_one_eq A.det

end PallLean.Paper93.DeepMath.NFrame
