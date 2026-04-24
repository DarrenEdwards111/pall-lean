import PallLean.Paper93.DeepMath.NFrame.EulerLagrange
import PallLean.Paper93.DeepMath.NFrame.SNFLambdaZero

namespace PallLean.Paper93.DeepMath.NFrame

/-- For β = λ = 0, `S_NF α 0 0 adj phi chi A = S_NF_alpha α adj phi`. -/
theorem S_NF_reduces_to_alpha_when_beta_lam_zero {n : ℕ} (α : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    S_NF α 0 0 adj phi chi A = S_NF_alpha α adj phi := by
  rw [S_NF_decompose]
  rw [show S_NF_beta 0 chi phi = 0 from by unfold S_NF_beta; ring]
  rw [show S_NF_lambda 0 A = 0 from by unfold S_NF_lambda; ring]
  ring

/-- When β = λ = 0, S_NF critical point (in Φ) coincides with critical point of S_NF_alpha. -/
theorem S_NF_alpha_critical_equiv_full {n : ℕ} (α : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) :
    IsEulerLagrangeCriticalPhi α 0 0 adj chi A phi ↔
      fderiv ℝ (fun psi => S_NF_alpha α adj psi) phi = 0 := by
  unfold IsEulerLagrangeCriticalPhi
  constructor
  · intro h
    rw [show (fun psi => S_NF α 0 0 adj psi chi A) =
         (fun psi => S_NF_alpha α adj psi) from by
      funext psi; exact S_NF_reduces_to_alpha_when_beta_lam_zero α adj psi chi A] at h
    exact h
  · intro h
    rw [show (fun psi => S_NF α 0 0 adj psi chi A) =
         (fun psi => S_NF_alpha α adj psi) from by
      funext psi; exact S_NF_reduces_to_alpha_when_beta_lam_zero α adj psi chi A]
    exact h

end PallLean.Paper93.DeepMath.NFrame
