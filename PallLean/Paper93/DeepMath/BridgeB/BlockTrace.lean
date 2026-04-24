import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic

namespace PallLean.Paper93.DeepMath.BridgeB

open Matrix

/-- Trace of a `blockDiagonal` matrix (with real entries and `Fin n` blocks indexed by `ι`)
equals the sum of the traces of the individual blocks. This is a direct specialisation of
`Matrix.trace_blockDiagonal`. -/
theorem blockDiagonal_trace
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (M : ι → Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.blockDiagonal M).trace = ∑ i, (M i).trace :=
  Matrix.trace_blockDiagonal M

end PallLean.Paper93.DeepMath.BridgeB
