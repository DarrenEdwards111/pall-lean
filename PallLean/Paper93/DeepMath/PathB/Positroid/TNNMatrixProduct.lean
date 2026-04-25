import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import PallLean.Paper93.DeepMath.PathB.Positroid.DiagonalNonnegTNN
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Product of two diagonal matrices is diagonal: `diagonal a * diagonal b = diagonal (a * b)`. -/
theorem diagonal_mul_diagonal_eq {n : ℕ} (a b : Fin n → ℝ) :
    Matrix.diagonal a * Matrix.diagonal b = Matrix.diagonal (a * b) :=
  Matrix.diagonal_mul_diagonal a b

/-- Product of two non-negative diagonal matrices is principal-TNN. -/
theorem diagonal_mul_diagonal_nonneg_isPrincipalTNN {n : ℕ}
    (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    IsPrincipalTNN (Matrix.diagonal a * Matrix.diagonal b) := by
  rw [diagonal_mul_diagonal_eq]
  apply diagonal_nonneg_isPrincipalTNN
  intro i
  exact mul_nonneg (ha i) (hb i)

/-- Product of identity and identity is identity (trivially TNN). -/
theorem identity_mul_identity_isPrincipalTNN (n : ℕ) :
    IsPrincipalTNN ((1 : Matrix (Fin n) (Fin n) ℝ) * (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  rw [Matrix.one_mul]
  exact identity_isPrincipalTNN n

/-- Two identity matrices multiplied gives identity. -/
theorem identity_mul_identity_eq_identity (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) ℝ) * (1 : Matrix (Fin n) (Fin n) ℝ) = 1 :=
  Matrix.one_mul _

end PallLean.Paper93.DeepMath.PathB.Positroid
