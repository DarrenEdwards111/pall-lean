import PallLean.Paper93.DeepMath.PathB.AlphaStrictPosOnKn
import PallLean.Paper93.DeepMath.PathB.MinimizerAtZeroKn

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame
open PallLean.Paper93.DeepMath.LPS

/-- For α > 0 and n ≥ 1, the α-term has UNIQUE minimum on K_n sum-zero subspace at Φ = 0:
    any nonzero sum-zero Φ has S_NF_alpha α K_n Φ > 0 = S_NF_alpha α K_n 0. -/
theorem alpha_unique_min_at_zero (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n)
    (phi : Fin n → ℝ) (hphi : ∑ i, phi i = 0) (hne : phi ≠ 0) :
    S_NF_alpha α (completeAdj n) 0 < S_NF_alpha α (completeAdj n) phi := by
  rw [alpha_min_at_zero_value α n (le_of_lt hα)]
  exact alpha_strict_pos α n hα hn phi hphi hne

end PallLean.Paper93.DeepMath.PathB
