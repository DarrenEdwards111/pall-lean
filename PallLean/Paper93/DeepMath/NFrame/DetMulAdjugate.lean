import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

/-!
# Jacobi identity: `A · adj(A) = det(A) · I` and the dual

This file exposes the two-sided Jacobi identity for real square matrices
indexed by `Fin n`, specialising Mathlib's general `Matrix.mul_adjugate`
and `Matrix.adjugate_mul`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- The Jacobi identity `A · adj(A) = det(A) · I`. Wraps Mathlib's `Matrix.mul_adjugate`. -/
theorem matrix_mul_adjugate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A * A.adjugate = A.det • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  exact Matrix.mul_adjugate A

/-- Dual: `adj(A) · A = det(A) · I`. -/
theorem adjugate_mul_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.adjugate * A = A.det • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  exact Matrix.adjugate_mul A

end PallLean.Paper93.DeepMath.NFrame
