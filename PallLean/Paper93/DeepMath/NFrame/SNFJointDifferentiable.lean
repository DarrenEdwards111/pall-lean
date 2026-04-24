import PallLean.Paper93.DeepMath.NFrame.SNFJointFDeriv
import PallLean.Paper93.DeepMath.NFrame.ParityPenaltyAtNoZero

namespace PallLean.Paper93.DeepMath.NFrame

/-- All three components of S_NF have well-defined differentiability at smooth points:
    α-term differentiable in Φ, β-term locally constant (hence ALL partials = 0) on no-zero Φ,
    λ-term differentiable on PosDef. This packages those three statements together. -/
theorem S_NF_smooth_differentiability {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ)
    (phi : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hphi : ∀ i, phi i ≠ 0) (hA : A.PosDef) :
    DifferentiableAt ℝ (fun psi : Fin n → ℝ => S_NF_alpha α adj psi) phi ∧
    (∀ k : Fin n, HasDerivAt (fun t => parityPenalty chi (Function.update phi k t)) 0 (phi k)) ∧
    DifferentiableAt ℝ (fun B : Matrix (Fin n) (Fin n) ℝ => S_NF_lambda lam B) A := by
  refine ⟨(S_NF_alpha_differentiable α adj).differentiableAt, ?_, S_NF_lambda_differentiableAt_posDef lam A hA⟩
  intros k
  exact parityPenalty_partial_zero_of_ne_zero chi phi k (hphi k)

end PallLean.Paper93.DeepMath.NFrame
