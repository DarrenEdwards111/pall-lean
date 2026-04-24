import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Eigenvalue properties for positive definite real matrices

Thin wrappers around Mathlib's spectral theory of Hermitian / positive
definite matrices, specialised to `Matrix (Fin n) (Fin n) ℝ`:

* `posDef_min_eigenvalue_pos`: for a positive definite matrix, every eigenvalue
  (in particular the smallest) is strictly positive.
* `posDef_sum_eigenvalues_eq_trace`: for a positive definite matrix, the sum of
  the eigenvalues equals the trace.

These wrap Mathlib's `Matrix.PosDef.eigenvalues_pos` and
`Matrix.IsHermitian.trace_eq_sum_eigenvalues`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- For `PosDef A`, the smallest eigenvalue is positive. Wraps
`Matrix.PosDef.eigenvalues_pos`. -/
theorem posDef_min_eigenvalue_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (i : Fin n) :
    0 < hA.1.eigenvalues i :=
  hA.eigenvalues_pos i

/-- For `PosDef A`, the sum of the eigenvalues equals the trace. Wraps
`Matrix.IsHermitian.trace_eq_sum_eigenvalues`. -/
theorem posDef_sum_eigenvalues_eq_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) :
    ∑ i, hA.1.eigenvalues i = A.trace := by
  have h : A.trace = ∑ i, ((hA.1.eigenvalues i : ℝ) : ℝ) :=
    Matrix.IsHermitian.trace_eq_sum_eigenvalues hA.1
  exact h.symm

end PallLean.Paper93.DeepMath.NFrame
