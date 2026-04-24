import Mathlib.Analysis.Matrix.PosDef

/-!
# PSD eigenvalues are nonnegative

Thin wrapper around Mathlib's `Matrix.PosSemidef.eigenvalues_nonneg`,
exposing the fact that every eigenvalue of a real positive
semi-definite (hence Hermitian / symmetric) matrix is nonnegative.
-/

namespace PallLean.Paper93.DeepMath.GraphSpectral

/-- For any real `N × N` matrix `M`, if `M` is positive semi-definite, then
every eigenvalue of its Hermitian spectral decomposition is nonnegative.

This is a direct wrapper around `Matrix.PosSemidef.eigenvalues_nonneg`
(Mathlib, `Mathlib/Analysis/Matrix/PosDef.lean`). The `Matrix.PosSemidef`
hypothesis already bundles the Hermitian (here, symmetric) condition via
its first projection `hPSD.1 : M.IsHermitian`, so no separate Hermitian
hypothesis is needed. -/
theorem psd_eig_nonneg {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (hPSD : M.PosSemidef) (i : Fin N) :
    0 ≤ hPSD.1.eigenvalues i :=
  hPSD.eigenvalues_nonneg i

/-- Existence-form corollary: a PSD matrix has a family of nonnegative
eigenvalues. Retained for backwards compatibility with earlier
Graph-Spectral clients that consumed the existential form. -/
theorem posSemidef_has_eigenvalues {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosSemidef) :
    ∃ es : Fin N → ℝ, ∀ i, 0 ≤ es i :=
  ⟨hA.1.eigenvalues, fun i => psd_eig_nonneg A hA i⟩

end PallLean.Paper93.DeepMath.GraphSpectral
