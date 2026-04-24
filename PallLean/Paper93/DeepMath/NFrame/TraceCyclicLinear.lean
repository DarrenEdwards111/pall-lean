import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.NFrame

/-- Trace is cyclic: `trace(A·B) = trace(B·A)`. -/
theorem trace_mul_cyclic {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A * B).trace = (B * A).trace := Matrix.trace_mul_comm A B

/-- Trace is linear in the matrix (additive). -/
theorem trace_add_distrib {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A + B).trace = A.trace + B.trace := Matrix.trace_add A B

/-- Trace distributes over smul. -/
theorem trace_smul {n : ℕ} (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    (c • A).trace = c * A.trace := Matrix.trace_smul c A

end PallLean.Paper93.DeepMath.NFrame
