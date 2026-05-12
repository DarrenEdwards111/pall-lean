import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Diagonal matrices with non-negative entries are principal-TNN

A diagonal matrix `D = Matrix.diagonal d` with `d i ≥ 0` for all `i` is
principal-TNN: every principal submatrix indexed by `J ⊆ Fin n` is itself
diagonal with entries `d j` for `j ∈ J`, so its determinant is the product
`∏_{j ∈ J} d j`, which is non-negative.

If additionally every `d i` is strictly positive, then `D` is principal-TP.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The principal submatrix of `Matrix.diagonal d` at `J` is the diagonal matrix
    with entries `d (j.val)` for `j ∈ J` (i.e. `d` restricted to `J`). -/
theorem submatrix_diagonal_principal {n : ℕ} (d : Fin n → ℝ) (J : Finset (Fin n)) :
    (Matrix.diagonal d).submatrix
        (fun i : J => (i.val : Fin n)) (fun j : J => (j.val : Fin n))
      = Matrix.diagonal (fun i : J => d i.val) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.submatrix_apply, Matrix.diagonal]
  · have h_val : (i.val : Fin n) ≠ j.val := fun heq => h (Subtype.ext heq)
    simp [Matrix.submatrix_apply, Matrix.diagonal_apply_ne _ h_val,
          Matrix.diagonal_apply_ne _ h]

/-- The determinant of a diagonal matrix is the product of diagonal entries. -/
theorem diagonal_det_prod {n : ℕ} (d : Fin n → ℝ) :
    (Matrix.diagonal d).det = ∏ i, d i :=
  Matrix.det_diagonal

/-- A diagonal matrix with non-negative diagonal entries is principal-TNN. -/
theorem diagonal_nonneg_isPrincipalTNN {n : ℕ} (d : Fin n → ℝ)
    (h : ∀ i, 0 ≤ d i) : IsPrincipalTNN (Matrix.diagonal d) := by
  intro J
  rw [submatrix_diagonal_principal, Matrix.det_diagonal]
  apply Finset.prod_nonneg
  intro i _
  exact h i.val

/-- A diagonal matrix with strictly positive diagonal entries is principal-TP. -/
theorem diagonal_pos_isPrincipalTP {n : ℕ} (d : Fin n → ℝ)
    (h : ∀ i, 0 < d i) : IsPrincipalTP (Matrix.diagonal d) := by
  intro J
  rw [submatrix_diagonal_principal, Matrix.det_diagonal]
  apply Finset.prod_pos
  intro i _
  exact h i.val

end PallLean.Paper93.DeepMath.PathB.Positroid
