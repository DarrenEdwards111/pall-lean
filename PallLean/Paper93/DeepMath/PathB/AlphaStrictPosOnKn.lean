import PallLean.Paper93.DeepMath.NFrame.SNFAlphaQuadForm

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame
open PallLean.Paper93.DeepMath.LPS

/-- Strict positivity: for α > 0 and nonzero sum-zero Φ on K_n with n ≥ 1,
    `S_NF_alpha α K_n Φ > 0`. -/
theorem alpha_strict_pos (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n)
    (phi : Fin n → ℝ) (hphi : ∑ i, phi i = 0) (hne : phi ≠ 0) :
    0 < S_NF_alpha α (completeAdj n) phi :=
  S_NF_alpha_Kn_pos_of_ne_zero α n hα hn phi hphi hne

end PallLean.Paper93.DeepMath.PathB
