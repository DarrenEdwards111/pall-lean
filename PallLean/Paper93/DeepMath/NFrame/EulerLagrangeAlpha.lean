import PallLean.Paper93.DeepMath.NFrame.SNFAlphaMinZero
import PallLean.Paper93.DeepMath.NFrame.SNFAlphaNonneg
import PallLean.Paper93.DeepMath.NFrame.EulerLagrange

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.LPS

/-- When β = λ = 0, the S_NF EL condition in Φ reduces to: Φ minimizes the α-term.
    For K_n sum-zero, this is equivalent to Φ = 0 (since α-term is strictly convex and 0
    is the unique minimum). -/
theorem S_NF_EL_reduces_to_alpha_min_Kn {n : ℕ} (α : ℝ) (hα : 0 ≤ α)
    (chi : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∀ phi, ∑ i, phi i = 0 →
      S_NF_alpha α (completeAdj n) 0 ≤ S_NF_alpha α (completeAdj n) phi := by
  intros phi hphi
  exact S_NF_alpha_Kn_min_zero α n hα phi hphi

end PallLean.Paper93.DeepMath.NFrame
