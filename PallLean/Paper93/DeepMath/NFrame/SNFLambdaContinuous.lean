import PallLean.Paper93.DeepMath.NFrame.SNF
import PallLean.Paper93.DeepMath.NFrame.BarrierContinuous

/-!
# Continuity of the λ-term `S_NF_lambda` on `{A | 0 < det A}`

We show that the λ-term of the N-Frame Lagrangian, namely
`S_NF_lambda lam A = lam * barrier A`, is continuous on the open locus
of positive-determinant matrices.

This is a direct consequence of
`barrier_continuousOn_det_pos` (from `BarrierContinuous.lean`) together
with continuity of scalar multiplication by a constant.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- `S_NF_lambda lam ·` is continuous on `{A | 0 < A.det}`. -/
theorem S_NF_lambda_continuousOn {n : ℕ} (lam : ℝ) :
    ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℝ => S_NF_lambda lam A)
                 {A : Matrix (Fin n) (Fin n) ℝ | 0 < A.det} := by
  unfold S_NF_lambda
  exact continuousOn_const.mul barrier_continuousOn_det_pos

end PallLean.Paper93.DeepMath.NFrame
