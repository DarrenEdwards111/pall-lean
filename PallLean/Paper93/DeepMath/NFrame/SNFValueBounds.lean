import PallLean.Paper93.DeepMath.NFrame.SNF
import PallLean.Paper93.DeepMath.NFrame.SNFBetaLSC
import PallLean.Paper93.DeepMath.NFrame.SNFAlphaNonneg

namespace PallLean.Paper93.DeepMath.NFrame

/-- On K_n with sum-zero Φ, α, β ≥ 0, and |χ_i| ≤ 1 per vertex, the α + β parts of S_NF are
    bounded between α-term and α-term + 2·β·n. -/
theorem S_NF_alpha_plus_beta_bounds {n : ℕ} (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (phi chi : Fin n → ℝ) (hphi : ∑ i, phi i = 0) (hchi : ∀ i, |chi i| ≤ 1) :
    S_NF_alpha α (PallLean.Paper93.DeepMath.LPS.completeAdj n) phi
      ≤ S_NF_alpha α (PallLean.Paper93.DeepMath.LPS.completeAdj n) phi + S_NF_beta β chi phi ∧
    S_NF_alpha α (PallLean.Paper93.DeepMath.LPS.completeAdj n) phi + S_NF_beta β chi phi
      ≤ S_NF_alpha α (PallLean.Paper93.DeepMath.LPS.completeAdj n) phi + β * (2 * n) := by
  constructor
  · have h := S_NF_beta_nonneg β hβ chi phi
    linarith
  · have h := parityPenalty_upper_bound chi phi hchi
    unfold S_NF_beta
    have : β * parityPenalty chi phi ≤ β * (2 * n) := by
      exact mul_le_mul_of_nonneg_left h hβ
    linarith

end PallLean.Paper93.DeepMath.NFrame
