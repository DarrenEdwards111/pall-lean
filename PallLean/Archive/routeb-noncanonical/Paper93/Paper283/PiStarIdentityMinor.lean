/-
  PallLean/Paper93/Paper283/PiStarIdentityMinor.lean

  Paper §28.3 — Π⋆ preserves the identity principal minor when the
  projection is full-rank. In the degenerate case where Π⋆ = 1, the
  conjugation `1 * 1 * 1ᵀ` simplifies to the identity, so the principal
  minor on any index set `J ⊆ Fin N` agrees with the identity minor and
  has determinant `1`.
-/

import PallLean.Paper93.Paper283.PrincipalMinor

namespace PallLean.Paper93.Paper283

open Matrix

/-- When Π⋆ has full range (P = 1), identity minors are preserved. -/
theorem piStarFromMatrix_preserves_identity_minor (N : ℕ)
    (J : Finset (Fin N)) :
    principalMinor ((1 : Matrix (Fin N) (Fin N) ℝ) * 1 * (1 : Matrix (Fin N) (Fin N) ℝ).transpose) J =
    principalMinor (1 : Matrix (Fin N) (Fin N) ℝ) J := by
  simp [Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul]

/-- Determinant of the identity-minor conjugation is `1`. -/
theorem piStarFromMatrix_identity_minor_det (N : ℕ) (J : Finset (Fin N)) :
    (principalMinor ((1 : Matrix (Fin N) (Fin N) ℝ) * 1 *
      (1 : Matrix (Fin N) (Fin N) ℝ).transpose) J).det = 1 := by
  rw [piStarFromMatrix_preserves_identity_minor, principalMinor_one_det]

end PallLean.Paper93.Paper283
