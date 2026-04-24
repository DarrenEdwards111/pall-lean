import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-!
# Positive scalar multiple of a positive semidefinite matrix (N-Frame)

Thin wrapper over `Matrix.PosSemidef.smul` specialised to real square matrices
indexed by `Fin n`.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Positive scalar multiple of a PosSemidef matrix is PosSemidef. -/
theorem posSemidef_smul_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hA : A.PosSemidef) :
    (c • A).PosSemidef :=
  hA.smul hc

end PallLean.Paper93.DeepMath.NFrame
