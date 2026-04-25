import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Eigenvector unitary: transpose-times-self equals identity (over ℝ)

For a real Hermitian (i.e. real symmetric) matrix `A`, Mathlib provides
`hA.eigenvectorUnitary` as an element of `Matrix.unitaryGroup n ℝ`. By the
unitary law we have `star U * U = 1`, and over `ℝ` (where `star` is trivial)
`star U` agrees with the transpose `Uᵀ`. Hence `Uᵀ * U = 1`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

open scoped Matrix

/-- For a real Hermitian matrix `A` on `Fin n`, the eigenvector unitary
`U := hA.eigenvectorUnitary.val` satisfies `Uᵀ * U = 1`.  Over the reals the
`star` operation is trivial, so the unitary identity `star U * U = 1` reduces
to a statement about the transpose. -/
theorem hermitian_eigenvectorUnitary_det_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) :
    ∃ (U : Matrix (Fin n) (Fin n) ℝ),
      U = hA.eigenvectorUnitary.val ∧ Uᵀ * U = 1 := by
  refine ⟨hA.eigenvectorUnitary.val, rfl, ?_⟩
  -- The unitary law gives `star U * U = 1`.
  have h₁ : star (hA.eigenvectorUnitary.val) * hA.eigenvectorUnitary.val = 1 :=
    Matrix.UnitaryGroup.star_mul_self hA.eigenvectorUnitary
  -- Over ℝ, `star U = Uᴴ = Uᵀ`.
  have h₂ : star (hA.eigenvectorUnitary.val) = (hA.eigenvectorUnitary.val)ᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [h₂] at h₁
  exact h₁

end PallLean.Paper93.DeepMath.NFrame
