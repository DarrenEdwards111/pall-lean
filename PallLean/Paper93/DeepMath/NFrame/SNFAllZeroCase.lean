import PallLean.Paper93.DeepMath.NFrame.SNF

namespace PallLean.Paper93.DeepMath.NFrame

/-- With α = β = λ = 0, S_NF is identically 0. -/
theorem S_NF_all_zero {n : ℕ} (adj : Matrix (Fin n) (Fin n) ℝ)
    (phi chi : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    S_NF 0 0 0 adj phi chi A = 0 := by
  rw [S_NF_decompose]
  unfold S_NF_alpha S_NF_beta S_NF_lambda
  ring

/-- With α = 0 = β and arbitrary λ: S_NF = λ · barrier A. -/
theorem S_NF_only_lambda {n : ℕ} (lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    S_NF 0 0 lam adj phi chi A = lam * barrier A := by
  rw [S_NF_decompose]
  unfold S_NF_alpha S_NF_beta S_NF_lambda
  ring

end PallLean.Paper93.DeepMath.NFrame
