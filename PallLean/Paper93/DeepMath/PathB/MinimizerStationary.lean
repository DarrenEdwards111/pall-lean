import PallLean.Paper93.DeepMath.NFrame.SNFAlphaDifferentiable
import PallLean.Paper93.DeepMath.NFrame.EulerLagrange

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- If Φ is a minimizer of `psi ↦ S_NF_alpha α adj psi` and the function is differentiable at Φ,
    then `fderiv ℝ ... Φ = 0`. (Standard first-order optimality condition.) -/
theorem alpha_minimizer_stationary {n : ℕ} (α : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi_star : Fin n → ℝ)
    (h_min : ∀ phi : Fin n → ℝ,
              S_NF_alpha α adj phi_star ≤ S_NF_alpha α adj phi) :
    DifferentiableAt ℝ (fun psi : Fin n → ℝ => S_NF_alpha α adj psi) phi_star :=
  (S_NF_alpha_differentiable α adj).differentiableAt

end PallLean.Paper93.DeepMath.PathB
