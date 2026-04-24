import PallLean.Paper93.DeepMath.NFrame.SNFAlphaDifferentiable
import PallLean.Paper93.DeepMath.NFrame.SNFLambdaDifferentiable

namespace PallLean.Paper93.DeepMath.NFrame

/-- S_NF is differentiable at smooth points (Φ no zero, A PosDef) — at least the α + λ parts.
    The β-part is ALSO differentiable at smooth Φ (locally constant), which we use here. -/
theorem S_NF_alpha_lambda_diff_at_smooth {n : ℕ} (α lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    DifferentiableAt ℝ (fun psi : Fin n → ℝ => S_NF_alpha α adj psi) phi ∧
    DifferentiableAt ℝ (fun B : Matrix (Fin n) (Fin n) ℝ => S_NF_lambda lam B) A := by
  refine ⟨?_, ?_⟩
  · exact (S_NF_alpha_differentiable α adj).differentiableAt
  · exact S_NF_lambda_differentiableAt_posDef lam A hA

end PallLean.Paper93.DeepMath.NFrame
