import PallLean.Paper93.DeepMath.NFrame.SNF
import PallLean.Paper93.DeepMath.NFrame.SNFAlphaNonneg

namespace PallLean.Paper93.DeepMath.NFrame

/-- With α, β ≥ 0 on K_n sum-zero Φ: `S_NF α β 0 K_n Φ χ A ≥ 0`. -/
theorem S_NF_alpha_beta_nonneg_on_Kn (α β : ℝ) (n : ℕ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (phi chi : Fin n → ℝ) (hphi : ∑ i, phi i = 0)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ S_NF α β 0 (PallLean.Paper93.DeepMath.LPS.completeAdj n) phi chi A := by
  rw [S_NF_decompose]
  have h_alpha : 0 ≤ S_NF_alpha α (PallLean.Paper93.DeepMath.LPS.completeAdj n) phi :=
    S_NF_alpha_Kn_nonneg α n hα phi hphi
  have h_beta : 0 ≤ S_NF_beta β chi phi := S_NF_beta_nonneg β hβ chi phi
  have h_lam : S_NF_lambda 0 A = 0 := by unfold S_NF_lambda; ring
  rw [h_lam, add_zero]
  linarith

end PallLean.Paper93.DeepMath.NFrame
