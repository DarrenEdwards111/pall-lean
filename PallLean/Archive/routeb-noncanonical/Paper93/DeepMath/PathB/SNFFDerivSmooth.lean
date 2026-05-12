import PallLean.Paper93.DeepMath.NFrame.SNFAlphaDifferentiable
import PallLean.Paper93.DeepMath.NFrame.SNFLambdaDifferentiable

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- For Φ with no zero entries and A PosDef, the α-term + λ-term FDerivs both exist.
    (β-term derivative = 0 at no-zero Φ; this is from `parityPenalty_partial_zero_of_ne_zero`.) -/
theorem S_NF_alpha_lambda_FDeriv_at_smooth {n : ℕ} (α lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    DifferentiableAt ℝ (fun psi : Fin n → ℝ => S_NF_alpha α adj psi) phi ∧
    DifferentiableAt ℝ (fun M : Matrix (Fin n) (Fin n) ℝ => S_NF_lambda lam M) A :=
  ⟨(S_NF_alpha_differentiable α adj).differentiableAt,
   S_NF_lambda_differentiableAt_posDef lam A hA⟩

end PallLean.Paper93.DeepMath.PathB
