import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import PallLean.Paper93.DeepMath.PathB.Positroid.DiagonalNonnegTNN
import Mathlib.Data.Matrix.Block

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- A diagonal matrix with all-ones is the identity. -/
theorem diagonal_all_ones_eq_identity (n : ℕ) :
    Matrix.diagonal (fun _ : Fin n => (1 : ℝ)) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.diagonal, Matrix.one_apply_eq]
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

/-- A diagonal matrix with all-ones is principal-TNN. -/
theorem diagonal_all_ones_isPrincipalTNN (n : ℕ) :
    IsPrincipalTNN (Matrix.diagonal (fun _ : Fin n => (1 : ℝ))) :=
  diagonal_nonneg_isPrincipalTNN _ (fun _ => by norm_num)

/-- Identity is the diagonal of all-ones (alternate phrasing). -/
theorem identity_eq_diagonal_ones (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) ℝ) = Matrix.diagonal (fun _ : Fin n => (1 : ℝ)) :=
  (diagonal_all_ones_eq_identity n).symm

end PallLean.Paper93.DeepMath.PathB.Positroid
