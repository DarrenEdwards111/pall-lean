import PallLean.Paper93.DeepMath.NFrame.SNFAlphaNonneg

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS

/-- For any M > 0 and sum-zero Φ on K_n with α > 0, if `∑ φᵢ² ≥ M/α·n`, then `S_NF_α ≥ M`. -/
theorem S_NF_alpha_Kn_lower_bound (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n)
    (phi : Fin n → ℝ) (hphi : ∑ i, phi i = 0)
    (M : ℝ) (hM : M ≤ α * (n : ℝ) * (∑ i, phi i * phi i)) :
    M ≤ S_NF_alpha α (completeAdj n) phi := by
  rw [S_NF_alpha_Kn_sumZero α n phi hphi]
  exact hM

end PallLean.Paper93.DeepMath.NFrame
