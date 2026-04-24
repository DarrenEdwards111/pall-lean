import PallLean.Paper93.DeepMath.NFrame.SNF
import PallLean.Paper93.DeepMath.NFrame.Barrier

namespace PallLean.Paper93.DeepMath.NFrame

/-- With `λ = 0`, the λ-term vanishes. -/
theorem S_NF_lambda_zero_coupling {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    S_NF_lambda 0 A = 0 := by
  unfold S_NF_lambda
  ring

/-- When `λ = 0`, `S_NF` reduces to `α·term + β·term`. -/
theorem S_NF_no_lambda {n : ℕ} (α β : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    S_NF α β 0 adj phi chi A = S_NF_alpha α adj phi + S_NF_beta β chi phi := by
  rw [S_NF_decompose, S_NF_lambda_zero_coupling, add_zero]

/-- For `A = identity`, the barrier vanishes (det I = 1). -/
theorem S_NF_lambda_at_identity {n : ℕ} (lam : ℝ) :
    S_NF_lambda lam (1 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  unfold S_NF_lambda
  rw [barrier_one]
  ring

/-- With `A = I`, S_NF reduces to α+β terms. -/
theorem S_NF_at_identity {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ) :
    S_NF α β lam adj phi chi 1 = S_NF_alpha α adj phi + S_NF_beta β chi phi := by
  rw [S_NF_decompose, S_NF_lambda_at_identity, add_zero]

end PallLean.Paper93.DeepMath.NFrame
