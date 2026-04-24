import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.GadgetRank

/-- Outer product `v ⊗ vᵀ` as a matrix: `(v ⊗ v) i j = v i * v j`. -/
def outer {n : ℕ} (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j => v i * v j)

/-- Outer product is symmetric. -/
theorem outer_isSymm {n : ℕ} (v : Fin n → ℝ) : (outer v).IsSymm := by
  ext i j
  simp [outer, Matrix.transpose_apply, mul_comm]

/-- Diagonal entries of the outer product are squares, hence ≥ 0. -/
theorem outer_diag_nonneg {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : 0 ≤ outer v i i := by
  show 0 ≤ v i * v i
  exact mul_self_nonneg (v i)

end PallLean.Paper93.DeepMath.GadgetRank
