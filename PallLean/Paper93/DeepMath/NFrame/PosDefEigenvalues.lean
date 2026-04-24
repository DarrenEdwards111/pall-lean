import Mathlib.Analysis.Matrix.PosDef

/-!
# Eigenvalue sign for positive (semi)definite real matrices

This file packages two thin wrappers around Mathlib's spectral theory of
Hermitian matrices, specialised to `Matrix (Fin n) (Fin n) ℝ`:

* `posDef_eigenvalues_pos`: a positive definite matrix has all eigenvalues
  strictly positive.
* `posSemidef_eigenvalues_nonneg`: a positive semi-definite matrix has all
  eigenvalues non-negative.

Both wrap the corresponding lemmas in `Mathlib.Analysis.Matrix.PosDef`:
`Matrix.PosDef.eigenvalues_pos` and `Matrix.PosSemidef.eigenvalues_nonneg`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- `PosDef` implies all eigenvalues are positive. Wraps Mathlib's
`Matrix.PosDef.eigenvalues_pos`. -/
theorem posDef_eigenvalues_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (i : Fin n) :
    0 < hA.1.eigenvalues i := hA.eigenvalues_pos i

/-- `PosSemidef` implies all eigenvalues are non-negative. Wraps Mathlib's
`Matrix.PosSemidef.eigenvalues_nonneg`. -/
theorem posSemidef_eigenvalues_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (i : Fin n) :
    0 ≤ hA.1.eigenvalues i := hA.eigenvalues_nonneg i

end PallLean.Paper93.DeepMath.NFrame
