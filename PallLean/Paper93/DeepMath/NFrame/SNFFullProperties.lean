import PallLean.Paper93.DeepMath.NFrame.SNF
import PallLean.Paper93.DeepMath.NFrame.SNFContinuousJoint
import PallLean.Paper93.DeepMath.NFrame.SNFAlphaDifferentiable
import PallLean.Paper93.DeepMath.NFrame.SNFLambdaDifferentiable

namespace PallLean.Paper93.DeepMath.NFrame

/-- The N-Frame Lagrangian is jointly continuous at smooth points. -/
theorem S_NF_continuous_at_smooth_full {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (chi : Fin n → ℝ)
    (phi : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hphi : ∀ i, phi i ≠ 0) (hA : 0 < A.det) :
    ContinuousAt (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin n) ℝ =>
      S_NF α β lam adj p.1 chi p.2) (phi, A) :=
  S_NF_continuousAt_smooth α β lam adj chi phi A hphi hA

/-- The α-term of the N-Frame Lagrangian is differentiable everywhere in Φ. -/
theorem S_NF_alpha_differentiable_full {n : ℕ} (α : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Differentiable ℝ (fun phi : Fin n → ℝ => S_NF_alpha α A phi) :=
  S_NF_alpha_differentiable α A

/-- The λ-term of the N-Frame Lagrangian is differentiable on PosDef. -/
theorem S_NF_lambda_differentiable_posDef_full {n : ℕ} (lam : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    DifferentiableAt ℝ (fun M => S_NF_lambda lam M) A :=
  S_NF_lambda_differentiableAt_posDef lam A hA

end PallLean.Paper93.DeepMath.NFrame
