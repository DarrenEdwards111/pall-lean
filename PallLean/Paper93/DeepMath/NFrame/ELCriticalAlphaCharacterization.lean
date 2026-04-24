import PallLean.Paper93.DeepMath.NFrame.EulerLagrange
import PallLean.Paper93.DeepMath.NFrame.SNFAlphaDifferentiable

namespace PallLean.Paper93.DeepMath.NFrame

/-- At β = λ = 0, an Euler-Lagrange critical point for Φ is exactly a vector where
    `fderiv ℝ (S_NF_alpha α adj) Φ = 0`. -/
theorem EL_critical_phi_alpha_only {n : ℕ} (α : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) :
    IsEulerLagrangeCriticalPhi α 0 0 adj chi A phi
      ↔ fderiv ℝ (fun psi => S_NF_alpha α adj psi) phi = 0 := by
  unfold IsEulerLagrangeCriticalPhi
  -- S_NF α 0 0 ... reduces to S_NF_alpha α adj psi pointwise
  constructor
  · intro h
    rw [show (fun psi => S_NF α 0 0 adj psi chi A) =
           (fun psi => S_NF_alpha α adj psi) from by
      funext psi
      unfold S_NF S_NF_alpha
      ring] at h
    exact h
  · intro h
    rw [show (fun psi => S_NF α 0 0 adj psi chi A) =
           (fun psi => S_NF_alpha α adj psi) from by
      funext psi
      unfold S_NF S_NF_alpha
      ring]
    exact h

end PallLean.Paper93.DeepMath.NFrame
