import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Pi

namespace PallLean.Paper93.DeepMath.GadgetRank

/-- The zero matrix's mulVec is zero. -/
theorem zero_mulVec_eq {m n : ℕ} (v : Fin n → ℝ) :
    (0 : Matrix (Fin m) (Fin n) ℝ).mulVec v = 0 := by
  ext i
  simp [Matrix.mulVec, Matrix.zero_apply, dotProduct,
        Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/-- A scalar multiple of the zero matrix is zero. -/
theorem smul_zero_matrix {m n : ℕ} (c : ℝ) :
    c • (0 : Matrix (Fin m) (Fin n) ℝ) = 0 := by
  simp

/-- Zero-vector and zero-matrix bilinear form is zero. -/
theorem zero_matrix_quad_form (n : ℕ) (v : Fin n → ℝ) :
    ∑ i, v i * ((0 : Matrix (Fin n) (Fin n) ℝ).mulVec v i) = 0 := by
  simp [zero_mulVec_eq, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

end PallLean.Paper93.DeepMath.GadgetRank
