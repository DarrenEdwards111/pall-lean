import PallLean.Paper93.DeepMath.NFrame.SNFAlphaMinZero
import PallLean.Paper93.DeepMath.NFrame.SNFAlphaGradient

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame
open PallLean.Paper93.DeepMath.LPS

/-- For α ≥ 0, the α-term on K_n sum-zero subspace is minimized at Φ = 0 with value 0. -/
theorem alpha_min_at_zero_value (α : ℝ) (n : ℕ) (hα : 0 ≤ α) :
    S_NF_alpha α (completeAdj n) 0 = 0 := by
  unfold S_NF_alpha
  simp [Matrix.mulVec_zero]

/-- And every sum-zero Φ has S_NF_alpha α K_n Φ ≥ 0 = S_NF_alpha α K_n 0. -/
theorem alpha_zero_global_min (α : ℝ) (n : ℕ) (hα : 0 ≤ α)
    (phi : Fin n → ℝ) (hphi : ∑ i, phi i = 0) :
    S_NF_alpha α (completeAdj n) 0 ≤ S_NF_alpha α (completeAdj n) phi := by
  rw [alpha_min_at_zero_value α n hα]
  exact S_NF_alpha_Kn_nonneg α n hα phi hphi

end PallLean.Paper93.DeepMath.PathB
