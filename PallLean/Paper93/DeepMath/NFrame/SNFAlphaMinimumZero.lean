import PallLean.Paper93.DeepMath.NFrame.SNFAlphaGradient
import PallLean.Paper93.DeepMath.NFrame.SNFAlphaMinZero

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.LPS

/-- Φ = 0 is a minimizer of `S_NF_alpha α K_n ·` on the sum-zero subspace for α ≥ 0. -/
theorem zero_is_minimizer_S_NF_alpha_Kn (α : ℝ) (n : ℕ) (hα : 0 ≤ α) :
    IsMinOn (fun phi : Fin n → ℝ => S_NF_alpha α (completeAdj n) phi)
            {phi | ∑ i, phi i = 0} 0 := by
  rw [isMinOn_iff]
  intros phi hphi
  simp only [Set.mem_setOf_eq] at hphi
  rw [S_NF_alpha_zero_eq]
  exact S_NF_alpha_Kn_nonneg α n hα phi hphi

end PallLean.Paper93.DeepMath.NFrame
