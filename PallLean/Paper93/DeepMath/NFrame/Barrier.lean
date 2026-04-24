import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# N-Frame Lagrangian barrier term (paper §28.3)

This file defines the scalar single-minor log-det barrier
`B(A) := -log(det A)` on square real matrices, together with its
basic algebraic identities.

The full paper §28.3 N-Frame Lagrangian barrier is a sum
`∑_{J ∈ 𝒥} -log(det A_J)` over an index family `𝒥` of principal
minors; here we record the single-minor scalar version that is
re-used by the scalar composition step (`DeepMathComposition`).

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- The single-matrix log-det barrier: `B(A) := -log(det A)`.

The full paper §28.3 barrier sums this over an index family `𝒥`
of principal minors; for scalar composition we use a single-minor
form. -/
noncomputable def barrier {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  -Real.log A.det

/-- Barrier vanishes when `det A = 1`. -/
theorem barrier_eq_zero_of_det_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : A.det = 1) : barrier A = 0 := by
  unfold barrier
  rw [h, Real.log_one, neg_zero]

/-- Barrier is a real number (trivial well-definedness statement). -/
theorem barrier_isReal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ r : ℝ, barrier A = r :=
  ⟨barrier A, rfl⟩

/-- Barrier of the identity matrix is `0`. -/
theorem barrier_one {n : ℕ} : barrier (1 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  apply barrier_eq_zero_of_det_one
  exact Matrix.det_one

end PallLean.Paper93.DeepMath.NFrame
