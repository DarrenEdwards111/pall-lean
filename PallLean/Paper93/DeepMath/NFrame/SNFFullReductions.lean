import PallLean.Paper93.DeepMath.NFrame.SNFLambdaZero
import PallLean.Paper93.DeepMath.NFrame.SNFAllZeroCase

namespace PallLean.Paper93.DeepMath.NFrame

/-- When β = 0 and λ = 0, S_NF reduces to S_NF_alpha only. -/
theorem S_NF_eq_alpha_when_beta_lambda_zero {n : ℕ} (α : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    S_NF α 0 0 adj phi chi A = S_NF_alpha α adj phi := by
  rw [S_NF_decompose]
  rw [show S_NF_beta 0 chi phi = 0 from by unfold S_NF_beta; ring]
  rw [show S_NF_lambda 0 A = 0 from by unfold S_NF_lambda; ring]
  ring

/-- When α = 0 and λ = 0, S_NF reduces to S_NF_beta only. -/
theorem S_NF_eq_beta_when_alpha_lambda_zero {n : ℕ} (β : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    S_NF 0 β 0 adj phi chi A = S_NF_beta β chi phi := by
  rw [S_NF_decompose]
  rw [show S_NF_alpha 0 adj phi = 0 from by unfold S_NF_alpha; ring]
  rw [show S_NF_lambda 0 A = 0 from by unfold S_NF_lambda; ring]
  ring

end PallLean.Paper93.DeepMath.NFrame
