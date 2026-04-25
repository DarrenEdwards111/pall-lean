import PallLean.Paper93.DeepMath.NFrame.SNFAlphaDifferentiable
import PallLean.Paper93.DeepMath.NFrame.EulerLagrange

namespace PallLean.Paper93.DeepMath.NFrame

/-- The α-term Φ-FDeriv exists everywhere. -/
theorem alpha_term_phi_fderiv_exists {n : ℕ} (α : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) :
    DifferentiableAt ℝ (fun psi : Fin n → ℝ => S_NF_alpha α A psi) phi :=
  (S_NF_alpha_differentiable α A).differentiableAt

/-- At a Φ-critical point of S_NF (β=λ=0), the α-FDeriv vanishes. -/
theorem alpha_fderiv_vanishes_at_critical {n : ℕ} (α : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ)
    (h : IsEulerLagrangeCriticalPhi α 0 0 adj chi A phi) :
    fderiv ℝ (fun psi : Fin n → ℝ => S_NF α 0 0 adj psi chi A) phi = 0 :=
  h

end PallLean.Paper93.DeepMath.NFrame
