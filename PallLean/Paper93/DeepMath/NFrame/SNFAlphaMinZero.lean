import PallLean.Paper93.DeepMath.NFrame.SNFAlphaNonneg
import PallLean.Paper93.DeepMath.NFrame.SNFAlphaGradient

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.LPS

/-- On K_n with sum-zero Φ and α ≥ 0, `S_NF_alpha α K_n Φ` is minimized at Φ = 0
    (where it equals 0). -/
theorem S_NF_alpha_Kn_min_zero (α : ℝ) (n : ℕ) (hα : 0 ≤ α) :
    ∀ phi : Fin n → ℝ, ∑ i, phi i = 0 →
      S_NF_alpha α (completeAdj n) (0 : Fin n → ℝ) ≤ S_NF_alpha α (completeAdj n) phi := by
  intros phi hphi
  rw [S_NF_alpha_zero_eq]
  exact S_NF_alpha_Kn_nonneg α n hα phi hphi

end PallLean.Paper93.DeepMath.NFrame
