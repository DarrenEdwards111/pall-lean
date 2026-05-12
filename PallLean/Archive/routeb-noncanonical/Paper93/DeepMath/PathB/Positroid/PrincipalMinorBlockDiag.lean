import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Principal minors of diagonal (block-diagonal) matrices

For a diagonal matrix `Matrix.diagonal d`, the principal submatrix at any index
set `J ⊆ Fin n` is itself diagonal with entries `d j.val` for `j ∈ J`, and so
its determinant (the principal minor) factors as the product
`∏_{j ∈ J} d j.val`.

This is the simplest instance of the general "block-diagonal principal minors
factor" pattern: when restricted to any block-respecting subset, the principal
minor is the product of per-block minors. For a (purely) diagonal matrix every
block is a 1×1 block, and the factorisation reduces to the product over `J`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- For a diagonal n×n matrix `diagonal d`, the determinant equals the product
    of diagonal entries. This is the standard `Matrix.det_diagonal`. -/
theorem diagonal_det_eq_prod {n : ℕ} (d : Fin n → ℝ) :
    (Matrix.diagonal d).det = ∏ i, d i :=
  Matrix.det_diagonal

/-- The principal submatrix of a diagonal matrix at index set J is itself a
    diagonal matrix on the smaller index type, with entries `d (j.val)` for j ∈ J. -/
theorem submatrix_diagonal_eq_diagonal {n : ℕ} (d : Fin n → ℝ) (J : Finset (Fin n)) :
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

/-- Principal minor of a diagonal matrix at J equals the product of diagonal entries indexed by J. -/
theorem diagonal_principalMinor_eq_prod {n : ℕ} (d : Fin n → ℝ) (J : Finset (Fin n)) :
    ((Matrix.diagonal d).submatrix
        (fun i : J => (i.val : Fin n)) (fun j : J => (j.val : Fin n))).det
      = ∏ i : J, d i.val := by
  rw [submatrix_diagonal_eq_diagonal, Matrix.det_diagonal]

end PallLean.Paper93.DeepMath.PathB.Positroid
