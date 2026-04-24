import PallLean.Paper93.DeepMath.GadgetRank.OuterProduct
import Mathlib.LinearAlgebra.Matrix.Trace

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.GadgetRank

/-- Trace of outer product `v ⊗ v = ∑ v_i²`. -/
theorem trace_outer {n : ℕ} (v : Fin n → ℝ) :
    (outer v).trace = ∑ i, v i * v i := by
  unfold outer
  simp [Matrix.trace]

end PallLean.Paper93.DeepMath.NFrame
