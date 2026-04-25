import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

/-!
# Cofactor (Laplacian) expansions of the determinant — N-Frame wrappers

Thin Mathlib wrappers specialised to real square matrices indexed by `Fin (n+1)`,
exposing the row-`0` and column-`0` cofactor expansions of the determinant under
N-Frame namespacing.

* `det_succ_row_zero_wrapper` — Laplacian expansion along row `0`.
* `det_succ_column_zero_wrapper` — Laplacian expansion along column `0`.

Both wrap the corresponding Mathlib lemmas
`Matrix.det_succ_row_zero` and `Matrix.det_succ_column_zero`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- For any matrix `A` and any row `i`, `det A` can be expanded along row `i` via cofactors.
    This is just Mathlib's `Matrix.det_succ_row` for `n+1` (paraphrased) or the row `0`
    specialisation. -/
theorem det_succ_row_zero_wrapper {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    A.det = ∑ j : Fin (n + 1),
              (-1)^(j : ℕ) * A 0 j * (A.submatrix Fin.succ j.succAbove).det :=
  Matrix.det_succ_row_zero A

/-- And dual along column `0`. -/
theorem det_succ_column_zero_wrapper {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    A.det = ∑ i : Fin (n + 1),
              (-1)^(i : ℕ) * A i 0 * (A.submatrix i.succAbove Fin.succ).det :=
  Matrix.det_succ_column_zero A

end PallLean.Paper93.DeepMath.NFrame
