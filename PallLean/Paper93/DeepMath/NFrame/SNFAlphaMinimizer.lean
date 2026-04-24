import PallLean.Paper93.DeepMath.NFrame.SumZeroBallCompact
import PallLean.Paper93.DeepMath.NFrame.SNFAlphaContinuous
import PallLean.Paper93.DeepMath.NFrame.ExistsMinOnCompact

namespace PallLean.Paper93.DeepMath.NFrame

/-- The α-term of S_NF attains its minimum on the closed ball of radius R intersected with
    the sum-zero subspace (nonempty compact + continuous ⇒ min exists). -/
theorem exists_min_S_NF_alpha_on_sumZero_ball {n : ℕ} (α : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ phi_star ∈ Metric.closedBall (0 : Fin n → ℝ) R ∩
                   {phi : Fin n → ℝ | ∑ i, phi i = 0},
      ∀ phi ∈ Metric.closedBall (0 : Fin n → ℝ) R ∩
                 {phi : Fin n → ℝ | ∑ i, phi i = 0},
        S_NF_alpha α A phi_star ≤ S_NF_alpha α A phi := by
  apply exists_minimum_on_compact
  · exact sumZeroBall_compact R hR
  · -- Nonempty: contains 0 which is in closedBall 0 R and in sum-zero.
    refine ⟨0, ?_, ?_⟩
    · exact Metric.mem_closedBall_self hR
    · simp [Finset.sum_const_zero]
  · -- Continuous
    exact (S_NF_alpha_continuous_in_phi α A).continuousOn

end PallLean.Paper93.DeepMath.NFrame
