import PallLean.Paper93.DeepMath.NFrame.SNF
import Mathlib.Topology.Algebra.Module.Basic

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.GraphSpectral

/-- For fixed α and adjacency A, the α-term of S_NF is continuous in Φ. -/
theorem S_NF_alpha_continuous_in_phi {n : ℕ} (α : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun phi : Fin n → ℝ => S_NF_alpha α A phi) := by
  unfold S_NF_alpha
  apply Continuous.mul continuous_const
  apply continuous_finset_sum
  intros i _
  apply Continuous.mul (continuous_apply i)
  -- (laplacian A).mulVec phi i is linear in phi hence continuous.
  -- Expand: (laplacian A).mulVec phi i = ∑ j, (laplacian A) i j * phi j
  simp only [Matrix.mulVec, dotProduct]
  apply continuous_finset_sum
  intros j _
  exact Continuous.mul continuous_const (continuous_apply j)

end PallLean.Paper93.DeepMath.NFrame
