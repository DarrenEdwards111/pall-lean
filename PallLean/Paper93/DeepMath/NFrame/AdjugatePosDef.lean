import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Real.Basic

/-!
# Adjugate formulas for invertible real matrices

This file packages the two standard identities relating the inverse and the
adjugate of a square real matrix whose determinant is a unit:

* `inv_eq_det_inv_smul_adjugate`:  `A⁻¹ = A.det⁻¹ • A.adjugate`.
* `adjugate_eq_det_smul_inv`:       `A.adjugate = A.det • A⁻¹`.

Both are stated for `Matrix (Fin n) (Fin n) ℝ` and wrap Mathlib's
`Matrix.inv_def` together with `Ring.inverse_eq_inv` on the field `ℝ`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- For a square real matrix `A` whose determinant is a unit,
`A⁻¹ = A.det⁻¹ • A.adjugate`. -/
theorem inv_eq_det_inv_smul_adjugate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit A.det) :
    A⁻¹ = A.det⁻¹ • A.adjugate := by
  -- `h` is unused here because on `ℝ` (a `GroupWithZero`) `Ring.inverse = Inv.inv`
  -- holds unconditionally.  We keep it in the signature to match the intended
  -- invertibility hypothesis.
  have _ : IsUnit A.det := h
  have h1 : A⁻¹ = Ring.inverse A.det • A.adjugate := Matrix.inv_def A
  have h2 : Ring.inverse A.det = A.det⁻¹ := Ring.inverse_eq_inv A.det
  rw [h1, h2]

/-- For a square real matrix `A` whose determinant is a unit,
`A.adjugate = A.det • A⁻¹`. -/
theorem adjugate_eq_det_smul_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsUnit A.det) :
    A.adjugate = A.det • A⁻¹ := by
  have hinv : A⁻¹ = A.det⁻¹ • A.adjugate := inv_eq_det_inv_smul_adjugate A h
  have hne : A.det ≠ 0 := IsUnit.ne_zero h
  calc A.adjugate
      = (1 : ℝ) • A.adjugate := by rw [one_smul]
    _ = (A.det * A.det⁻¹) • A.adjugate := by
          rw [mul_inv_cancel₀ hne]
    _ = A.det • (A.det⁻¹ • A.adjugate) := by
          rw [← smul_assoc, smul_eq_mul]
    _ = A.det • A⁻¹ := by rw [← hinv]

end PallLean.Paper93.DeepMath.NFrame
