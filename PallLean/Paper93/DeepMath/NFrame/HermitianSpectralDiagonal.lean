import Mathlib.Analysis.Matrix.Spectrum

/-!
# Hermitian spectral diagonalisation wrappers

Thin wrappers around Mathlib's `Matrix.IsHermitian.eigenvectorUnitary`
for real Hermitian matrices on `Fin n`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- From Mathlib: the `eigenvectorUnitary` exists for Hermitian matrices. -/
theorem hermitian_eigenvectorUnitary_exists {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, U = hA.eigenvectorUnitary.val :=
  ⟨hA.eigenvectorUnitary.val, rfl⟩

/-- Alternative form: the `eigenvectorUnitary` matrix exists and equals itself. -/
theorem hermitian_eigenvector_unitary_exists_alt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, U = hA.eigenvectorUnitary.val :=
  ⟨hA.eigenvectorUnitary.val, rfl⟩

end PallLean.Paper93.DeepMath.NFrame
