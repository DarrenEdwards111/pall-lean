import PallLean.Paper93.DeepMath.NFrame.SNFAtZero
import PallLean.Paper93.DeepMath.NFrame.Barrier

namespace PallLean.Paper93.DeepMath.NFrame

/-- Value of S_NF at Φ = 0 and A = I (identity): only β-term survives (α-term and λ-term vanish). -/
theorem S_NF_at_origin_identity {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ) :
    S_NF α β lam adj (0 : Fin n → ℝ) chi (1 : Matrix (Fin n) (Fin n) ℝ) = β * n := by
  rw [S_NF_decompose]
  rw [S_NF_alpha_zero α adj]  -- α-term = 0
  rw [S_NF_beta_zero β chi]    -- β-term = β·n
  have h_lam_at_one : S_NF_lambda lam (1 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
    unfold S_NF_lambda
    rw [barrier_one]
    ring
  rw [h_lam_at_one]
  ring

end PallLean.Paper93.DeepMath.NFrame
