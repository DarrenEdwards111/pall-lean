import PallLean.Paper93.DeepMath.NFrame.SNF
import PallLean.Paper93.DeepMath.NFrame.BarrierDifferentiable

open scoped Matrix.Norms.Elementwise

namespace PallLean.Paper93.DeepMath.NFrame

/-- `S_NF_lambda lam` is differentiable at any A with det A ≠ 0. -/
theorem S_NF_lambda_differentiableAt_of_det_ne_zero {n : ℕ} (lam : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (h : A.det ≠ 0) :
    DifferentiableAt ℝ (fun M => S_NF_lambda lam M) A := by
  unfold S_NF_lambda
  exact (barrier_differentiableAt_of_det_ne_zero A h).const_mul _

/-- `S_NF_lambda lam` differentiable at every PosDef A. -/
theorem S_NF_lambda_differentiableAt_posDef {n : ℕ} (lam : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    DifferentiableAt ℝ (fun M => S_NF_lambda lam M) A :=
  S_NF_lambda_differentiableAt_of_det_ne_zero lam A (ne_of_gt hA.det_pos)

end PallLean.Paper93.DeepMath.NFrame
