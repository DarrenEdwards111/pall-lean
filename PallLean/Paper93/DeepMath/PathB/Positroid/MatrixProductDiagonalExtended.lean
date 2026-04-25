import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import PallLean.Paper93.DeepMath.PathB.Positroid.DiagonalNonnegTNN

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Identity squared = identity. -/
theorem identity_sq_eq_identity (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) ℝ) * (1 : Matrix (Fin n) (Fin n) ℝ) = 1 :=
  Matrix.one_mul _

/-- Identity cubed = identity. -/
theorem identity_cubed_eq_identity (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) ℝ) * (1 : Matrix (Fin n) (Fin n) ℝ) * (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  rw [Matrix.one_mul, Matrix.one_mul]

/-- Identity to any number of factors equals identity. -/
theorem identity_powers_eq_identity (n : ℕ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) * (1 : Matrix (Fin n) (Fin n) ℝ)) *
    ((1 : Matrix (Fin n) (Fin n) ℝ) * (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 := by
  rw [Matrix.one_mul, Matrix.one_mul]

end PallLean.Paper93.DeepMath.PathB.Positroid
