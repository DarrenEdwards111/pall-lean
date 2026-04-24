import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Real.Basic

/-!
# Transpose and inverse commute (N-Frame)

Thin Mathlib wrappers providing the identity `(A⁻¹)ᵀ = (Aᵀ)⁻¹` in
both directions, together with the symmetric-matrix consequence
`(A⁻¹)ᵀ = A⁻¹` when `A.IsSymm`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

open Matrix

/-- Transpose of matrix inverse equals inverse of transpose (for nonsingular matrix). -/
theorem inv_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (_h : IsUnit A.det) :
    (A⁻¹)ᵀ = (Aᵀ)⁻¹ := by
  exact Matrix.transpose_nonsing_inv A

/-- `(Aᵀ)⁻¹ = (A⁻¹)ᵀ` form. -/
theorem transpose_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Aᵀ)⁻¹ = (A⁻¹)ᵀ := by
  rw [Matrix.transpose_nonsing_inv]

/-- For symmetric `A`, `(A⁻¹)ᵀ = A⁻¹`. -/
theorem inv_transpose_of_isSymm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    (A⁻¹)ᵀ = A⁻¹ := by
  rw [Matrix.transpose_nonsing_inv]
  -- After rewrite, goal is `Aᵀ⁻¹ = A⁻¹`.
  -- Use `IsSymm : Aᵀ = A` to finish.
  unfold Matrix.IsSymm at hA
  congr 1

end PallLean.Paper93.DeepMath.NFrame
