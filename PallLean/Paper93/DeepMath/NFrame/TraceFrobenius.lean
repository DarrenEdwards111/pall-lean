import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Defs

namespace PallLean.Paper93.DeepMath.NFrame

open Matrix

/-- Trace of `Mᵀ * M` equals the sum of squared entries of M (Frobenius norm squared). -/
theorem trace_transpose_mul_self_eq_sum_sq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    (Mᵀ * M).trace = ∑ i, ∑ j, (M i j)^2 := by
  have expand : (Mᵀ * M).trace = ∑ i, ∑ k, Mᵀ i k * M k i := by
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intros i _
    show (Mᵀ * M) i i = _
    simp [Matrix.mul_apply]
  rw [expand]
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intros j _
  apply Finset.sum_congr rfl
  intros i _
  ring

/-- Trace of `Mᵀ * M` is nonneg (Frobenius inner product of M with itself). -/
theorem trace_transpose_mul_self_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ (Mᵀ * M).trace := by
  rw [trace_transpose_mul_self_eq_sum_sq]
  apply Finset.sum_nonneg
  intros i _
  apply Finset.sum_nonneg
  intros j _
  exact sq_nonneg _

end PallLean.Paper93.DeepMath.NFrame
