import PallLean.Paper93.DeepMath.NFrame.AdjTraceBilinear
import PallLean.Paper93.DeepMath.NFrame.TraceScalarMul

namespace PallLean.Paper93.DeepMath.NFrame

/-- `adjTraceAt A A = trace(adj A · A) = det A · n`.
    This is Euler's identity: det is a homogeneous-n polynomial, so the gradient at A applied
    to A itself gives n·det A. -/
theorem adjTraceAt_self_eq_n_mul_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    adjTraceAt A A = (n : ℝ) * A.det := by
  unfold adjTraceAt
  rw [Matrix.adjugate_mul, trace_smul_one_eq, mul_comm]

end PallLean.Paper93.DeepMath.NFrame
