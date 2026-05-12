import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Scalar multiplication preserves principal-TNN / principal-TP

If `A` is principal-TNN and `c ≥ 0`, then `c • A` is principal-TNN. Likewise,
if `A` is principal-TP and `c > 0`, then `c • A` is principal-TP.

The proof proceeds by:
  * showing scalar multiplication commutes with taking principal submatrices
    (a definitional `rfl` after `ext`),
  * applying `Matrix.det_smul` to express
    `det (c • M) = c ^ (card J) * det M`,
  * concluding with `mul_nonneg` / `mul_pos` and `pow_nonneg` / `pow_pos`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Scalar multiplication commutes with principal submatrix. -/
theorem submatrix_smul_principal {n : ℕ} (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (J : Finset (Fin n)) :
    (c • A).submatrix (fun i : J => (i.val : Fin n)) (fun j : J => (j.val : Fin n))
      = c • (A.submatrix (fun i : J => (i.val : Fin n)) (fun j : J => (j.val : Fin n))) := by
  ext i j
  rfl

/-- Non-negative scalar multiplication preserves principal-TNN. -/
theorem IsPrincipalTNN.smul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (h : IsPrincipalTNN A) {c : ℝ} (hc : 0 ≤ c) :
    IsPrincipalTNN (c • A) := by
  intro J
  rw [submatrix_smul_principal]
  rw [Matrix.det_smul]
  apply mul_nonneg
  · exact pow_nonneg hc _
  · exact h J

/-- Strictly positive scalar multiplication preserves principal-TP. -/
theorem IsPrincipalTP.smul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (h : IsPrincipalTP A) {c : ℝ} (hc : 0 < c) :
    IsPrincipalTP (c • A) := by
  intro J
  rw [submatrix_smul_principal]
  rw [Matrix.det_smul]
  apply mul_pos
  · exact pow_pos hc _
  · exact h J

end PallLean.Paper93.DeepMath.PathB.Positroid
