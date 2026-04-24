import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-!
# Convex combinations of positive-definite matrices (N-Frame)

Let `A`, `B : Matrix (Fin n) (Fin n) ℝ` be positive definite and
`t ∈ (0,1)`. Then the convex combination `(1 - t) • A + t • B` is
again positive definite.

The proof packages Mathlib's `Matrix.PosDef.smul` (positive scaling
preserves `PosDef`) together with `Matrix.PosDef.add` (the sum of two
`PosDef` matrices is `PosDef`) into a single wrapper.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Convex combination of two `PosDef` matrices (with strictly positive
weights `1-t` and `t`, both in `(0,1)`) is `PosDef`. -/
theorem posDef_convex_comb {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (t : ℝ) (h0 : 0 < t) (h1 : t < 1) :
    ((1 - t) • A + t • B).PosDef := by
  have h1mt : (0 : ℝ) < 1 - t := by linarith
  exact (hA.smul h1mt).add (hB.smul h0)

end PallLean.Paper93.DeepMath.NFrame
