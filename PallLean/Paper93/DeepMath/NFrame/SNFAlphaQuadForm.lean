import PallLean.Paper93.DeepMath.NFrame.SNFAlphaNonneg

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS

/-- On K_n sum-zero subspace, `S_NF_alpha α K_n Φ = α·n·‖Φ‖²`.
    For α > 0 and n ≥ 1, this is strictly positive for nonzero Φ. -/
theorem S_NF_alpha_Kn_pos_of_ne_zero (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n)
    (phi : Fin n → ℝ) (hphi : ∑ i, phi i = 0) (hne : phi ≠ 0) :
    0 < S_NF_alpha α (completeAdj n) phi := by
  rw [S_NF_alpha_Kn_sumZero α n phi hphi]
  have h_n_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_sum_pos : 0 < ∑ i, phi i * phi i := sum_sq_pos_of_ne_zero phi hne
  positivity

end PallLean.Paper93.DeepMath.NFrame
