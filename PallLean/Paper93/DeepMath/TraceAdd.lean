import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic

namespace PallLean.Paper93.DeepMath

theorem matrix_trace_add :
    ∀ {N} (A B : Matrix (Fin N) (Fin N) ℝ), (A + B).trace = A.trace + B.trace := by
  intro N A B
  exact Matrix.trace_add A B

end PallLean.Paper93.DeepMath
