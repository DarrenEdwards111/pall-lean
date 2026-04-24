import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Determinant and log-determinant of positive definite matrices

For a positive definite matrix `A : Matrix (Fin n) (Fin n) ℝ`, the determinant
equals the product of its (Hermitian) eigenvalues, and therefore the logarithm
of the determinant equals the sum of the logarithms of the eigenvalues.

These are thin wrappers around Mathlib's
`Matrix.IsHermitian.det_eq_prod_eigenvalues` and `Real.log_prod`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- For a positive definite real matrix `A`, `det A = ∏ i, eigenvalues A i`.
Wraps Mathlib's `Matrix.IsHermitian.det_eq_prod_eigenvalues`, where the
ambient scalar field `𝕜 = ℝ` makes the `RCLike.ofReal` coercion a no-op. -/
theorem det_posDef_eq_prod_eigenvalues {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) :
    A.det = ∏ i, hA.1.eigenvalues i := by
  have h := hA.1.det_eq_prod_eigenvalues
  -- `(hA.1.eigenvalues i : ℝ)` is the RCLike.ofReal coercion from ℝ to ℝ,
  -- which is definitionally the identity; `simp` closes the resulting goal.
  simpa using h

/-- For a positive definite real matrix `A`,
`log (det A) = ∑ i, log (eigenvalues A i)`. -/
theorem log_det_posDef_eq_sum_log_eigenvalues {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    Real.log A.det = ∑ i, Real.log (hA.1.eigenvalues i) := by
  rw [det_posDef_eq_prod_eigenvalues A hA]
  apply Real.log_prod
  intro i _
  exact (hA.eigenvalues_pos i).ne'

end PallLean.Paper93.DeepMath.NFrame
