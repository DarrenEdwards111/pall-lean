import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.NFrame

/-- Explicit formula: `trace(A * B) = ∑ᵢ ∑ⱼ A_ij · B_ji`. -/
theorem trace_mul_eq_sum {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A * B).trace = ∑ i, ∑ j, A i j * B j i := by
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intros i _
  show (A * B) i i = _
  simp [Matrix.mul_apply]

/-- Trace of adjugate times a matrix in explicit form. -/
theorem trace_adjugate_mul_eq_sum {n : ℕ} (A M : Matrix (Fin n) (Fin n) ℝ) :
    (A.adjugate * M).trace = ∑ i, ∑ j, A.adjugate i j * M j i :=
  trace_mul_eq_sum A.adjugate M

end PallLean.Paper93.DeepMath.NFrame
