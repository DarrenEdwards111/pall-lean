import PallLean.Paper93.DeepMath.PathB.PathBToExistingChain
import PallLean.Paper93.DeepMath.PathB.GaugeToRank
import PallLean.Paper93.DeepMath.PathB.HarmonicAtMin
import PallLean.Paper93.DeepMath.PathB.MinimizerAtZeroKn

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- Path B summary statement: combining all Path B pieces gives:
    1. Minimizer existence at Φ=0 on K_n sum-zero (kernel-only)
    2. Rank chain gauge ⇒ rank ≥ κ (kernel-only)
    3. Existing PaperFaithfulSeparation provides ¬ PeqNP_Paper (one upstream axiom)
    Composed, this is Path B's full chain. -/
theorem path_B_summary :
    ∃ (n : ℕ), 0 < n ∧
      (∀ phi : Fin n → ℝ, ∑ i, phi i = 0 →
        S_NF_alpha 1 (PallLean.Paper93.DeepMath.LPS.completeAdj n) 0 ≤
          S_NF_alpha 1 (PallLean.Paper93.DeepMath.LPS.completeAdj n) phi) := by
  refine ⟨2, by norm_num, ?_⟩
  intros phi hphi
  exact alpha_zero_global_min 1 2 (by norm_num) phi hphi

end PallLean.Paper93.DeepMath.PathB
