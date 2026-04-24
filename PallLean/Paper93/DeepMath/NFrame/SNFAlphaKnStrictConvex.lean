import PallLean.Paper93.DeepMath.NFrame.SNFAlphaHomogeneous
import PallLean.Paper93.DeepMath.NFrame.SNFAlphaNonneg

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GadgetRank

/-- For α > 0 and n ≥ 1, the α-term on K_n sum-zero subspace is strictly positive at any nonzero Φ. -/
theorem S_NF_alpha_Kn_pos_iff_ne_zero (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n)
    (phi : Fin n → ℝ) (hphi : ∑ i, phi i = 0) :
    phi = 0 ∨ 0 < S_NF_alpha α (completeAdj n) phi := by
  by_cases h : phi = 0
  · left; exact h
  · right
    rw [S_NF_alpha_Kn_sumZero α n phi hphi]
    have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have h_sum_pos : 0 < ∑ i, phi i * phi i := sum_sq_pos_of_ne_zero phi h
    positivity

end PallLean.Paper93.DeepMath.NFrame
