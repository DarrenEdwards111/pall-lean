import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath.BridgeB

open scoped BigOperators

/-- Determinant of a block diagonal matrix (indexed by a `Fintype`) equals the
product of the determinants of the blocks. This is a direct wrapper around
`Matrix.det_blockDiagonal` from Mathlib. -/
theorem det_blockDiagonal_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (M : ι → Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.blockDiagonal M).det = ∏ i, (M i).det :=
  Matrix.det_blockDiagonal M

end PallLean.Paper93.DeepMath.BridgeB
