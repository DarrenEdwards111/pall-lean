import Mathlib.Analysis.Matrix.Spectrum

/-!
# Spectral theorem wrappers for real Hermitian matrices

This file packages thin wrappers around Mathlib's spectral theory of
Hermitian matrices, specialised to `Matrix (Fin n) (Fin n) ℝ`:

* `isHermitian_eigenvalues`: existence of eigenvalues for a Hermitian matrix.
* `sum_eigenvalues_eq_trace`: the sum of the eigenvalues equals the trace.

Both wrap Mathlib's `Matrix.IsHermitian.eigenvalues` and
`Matrix.IsHermitian.trace_eq_sum_eigenvalues`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- For Hermitian `M : Matrix (Fin n) (Fin n) ℝ`, there exist eigenvalues and eigenvectors
    summing to the spectral decomposition. Wraps Mathlib's `Matrix.IsHermitian.spectral_theorem`
    or `.eigenvalues`. -/
theorem isHermitian_eigenvalues {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (i : Fin n) :
    ∃ (lam : ℝ), hA.eigenvalues i = lam := ⟨hA.eigenvalues i, rfl⟩

/-- Sum of eigenvalues equals trace for Hermitian matrix. Wraps Mathlib's
    `Matrix.IsHermitian.trace_eq_sum_eigenvalues`. -/
theorem sum_eigenvalues_eq_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) :
    ∑ i, hA.eigenvalues i = A.trace := by
  have h : A.trace = ∑ i, ((hA.eigenvalues i : ℝ) : ℝ) :=
    Matrix.IsHermitian.trace_eq_sum_eigenvalues hA
  exact h.symm

end PallLean.Paper93.DeepMath.NFrame
