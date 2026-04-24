import PallLean.Paper93.DeepMath.NFrame.SNFAlphaMinimizer
import PallLean.Paper93.DeepMath.NFrame.SNFAlphaContinuous
import PallLean.Paper93.DeepMath.LPS.KnLaplacianSumZeroQuad

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.LPS

/-- The α-term of S_NF on sum-zero ball × {any A} attains its minimum.
    Since α-term doesn't depend on A, this reduces to the α-term-alone minimization. -/
theorem exists_min_S_NF_alpha_on_sumZero_ball_any_A {n : ℕ} (α : ℝ)
    (A_fixed : Matrix (Fin n) (Fin n) ℝ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ phi_star ∈ Metric.closedBall (0 : Fin n → ℝ) R ∩
                   {phi : Fin n → ℝ | ∑ i, phi i = 0},
      ∀ phi ∈ Metric.closedBall (0 : Fin n → ℝ) R ∩
                 {phi : Fin n → ℝ | ∑ i, phi i = 0},
        S_NF_alpha α A_fixed phi_star ≤ S_NF_alpha α A_fixed phi :=
  exists_min_S_NF_alpha_on_sumZero_ball α A_fixed R hR

end PallLean.Paper93.DeepMath.NFrame
