import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.NFrame

/-- The trace function as a linear map. -/
noncomputable def traceLinearMap (n : ℕ) : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
  Matrix.traceLinearMap (Fin n) ℝ ℝ

/-- Trace commutes with addition via LinearMap. -/
theorem traceLinearMap_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    traceLinearMap n A = A.trace :=
  rfl

end PallLean.Paper93.DeepMath.NFrame
