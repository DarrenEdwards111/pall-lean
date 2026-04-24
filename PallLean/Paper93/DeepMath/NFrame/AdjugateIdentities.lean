import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

/-!
# Adjugate identities (N-Frame)

Thin Mathlib wrappers specialised to real square matrices indexed by `Fin n`:

* `adjugate_mul_self` — `adj(A) · A = det A · I` (dual of `A · adj A = det A · I`).
* `det_adjugate_formula` — `det(adj A) = (det A)^(n-1)`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- `adj(A) · A = det A · I`. (Dual of `A · adj A = det A · I`.) -/
theorem adjugate_mul_self {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.adjugate * A = A.det • (1 : Matrix (Fin n) (Fin n) ℝ) :=
  Matrix.adjugate_mul A

/-- `det(adj A) = (det A)^(n-1)`. Wraps Mathlib's `Matrix.det_adjugate`. -/
theorem det_adjugate_formula {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.adjugate.det = A.det ^ (n - 1) := by
  rw [Matrix.det_adjugate A]
  simp [Fintype.card_fin]

end PallLean.Paper93.DeepMath.NFrame
