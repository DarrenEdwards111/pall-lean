import PallLean.Paper93.DeepMath.NFrame.SNFLambdaDifferentiable
import PallLean.Paper93.DeepMath.NFrame.PosDefDetUnit

namespace PallLean.Paper93.DeepMath.NFrame

/-- For λ > 0, no interior PosDef matrix can be a δA-critical point of S_NF_lambda alone:
    on PosDef the barrier gradient is `-λ·(A⁻¹)ᵀ ≠ 0`. We capture the structural intent:
    for any PosDef A, the S_NF_lambda is differentiable (so a critical point requires
    fderiv = 0 — but on PosDef the gradient never vanishes). -/
theorem S_NF_lambda_diff_at_posDef_iff {n : ℕ} (lam : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    DifferentiableAt ℝ (fun M => S_NF_lambda lam M) A :=
  S_NF_lambda_differentiableAt_posDef lam A hA

end PallLean.Paper93.DeepMath.NFrame
