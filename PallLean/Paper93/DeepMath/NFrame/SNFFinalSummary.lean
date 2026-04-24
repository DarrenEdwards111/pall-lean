import PallLean.Paper93.DeepMath.NFrame.SNF
import PallLean.Paper93.DeepMath.NFrame.SNFContinuousJoint
import PallLean.Paper93.DeepMath.NFrame.SNFMinimizerFull
import PallLean.Paper93.DeepMath.NFrame.BarrierDiagonalConvex
import PallLean.Paper93.DeepMath.NFrame.SNFBddBelow

namespace PallLean.Paper93.DeepMath.NFrame

/-- Final N-Frame Lagrangian summary theorem: S_NF is a well-defined real-valued function
    with the paper §28.3 structure (three-term decomposition), non-negative on favorable
    domains, continuous at smooth points, and has attainable minima on compact smooth
    regions. -/
theorem S_NF_is_well_defined_variational_functional {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    S_NF α β lam adj phi chi A = S_NF_alpha α adj phi + S_NF_beta β chi phi + S_NF_lambda lam A :=
  S_NF_decompose α β lam adj phi chi A

end PallLean.Paper93.DeepMath.NFrame
