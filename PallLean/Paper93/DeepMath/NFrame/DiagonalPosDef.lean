import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-!
# Positive (semi)definiteness of real diagonal matrices (N-Frame)

Thin wrappers over Mathlib's `Matrix.PosDef.diagonal` /
`Matrix.PosSemidef.diagonal` specialised to `Fin n → ℝ`:

* `diagonal_posDef`    : all-positive entries ⇒ `PosDef`.
* `diagonal_posSemidef`: all-nonnegative entries ⇒ `PosSemidef`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Diagonal matrix with all positive entries is positive definite. -/
theorem diagonal_posDef {n : ℕ} (d : Fin n → ℝ) (h : ∀ i, 0 < d i) :
    (Matrix.diagonal d).PosDef :=
  Matrix.PosDef.diagonal h

/-- Diagonal matrix with all nonnegative entries is positive semidefinite. -/
theorem diagonal_posSemidef {n : ℕ} (d : Fin n → ℝ) (h : ∀ i, 0 ≤ d i) :
    (Matrix.diagonal d).PosSemidef :=
  Matrix.PosSemidef.diagonal h

end PallLean.Paper93.DeepMath.NFrame
