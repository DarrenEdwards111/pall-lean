import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Real.Basic

/-!
# Positive definite implies symmetric; transpose preserves PosDef (N-Frame)

Real-matrix wrappers around the Mathlib `Matrix.PosDef` API:

* `posDef_isSymm` : a real PosDef matrix is symmetric (`Aᵀ = A`).
* `posDef_transpose` : transpose of a real PosDef matrix is PosDef.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

open Matrix

/-- PosDef implies Hermitian (symmetric for real matrices). -/
theorem posDef_isSymm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    A.IsSymm := by
  have hHerm : A.IsHermitian := hA.1
  unfold Matrix.IsHermitian at hHerm
  unfold Matrix.IsSymm
  -- Over ℝ, conjTranspose = transpose.
  have hEq : A.conjTranspose = A.transpose := by
    ext i j; simp [Matrix.conjTranspose_apply, star_trivial]
  rw [hEq] at hHerm
  exact hHerm

/-- Transpose of PosDef is PosDef (for real matrices: PosDef is preserved under transpose
    because PosDef ⇒ symmetric, and symmetric transpose equals self). -/
theorem posDef_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    (Aᵀ).PosDef := by
  have hSymm := posDef_isSymm A hA
  have hTA : Aᵀ = A := hSymm
  rw [hTA]
  exact hA

end PallLean.Paper93.DeepMath.NFrame
