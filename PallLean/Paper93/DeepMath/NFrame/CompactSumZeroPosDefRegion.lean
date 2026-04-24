import PallLean.Paper93.DeepMath.NFrame.SumZeroBallCompact
import PallLean.Paper93.DeepMath.NFrame.PosDefDetBall
import PallLean.Paper93.DeepMath.NFrame.ProductCompact

namespace PallLean.Paper93.DeepMath.NFrame

open scoped Matrix.Norms.Elementwise

/-- The product of (sum-zero ∩ closed ball in ℝⁿ) × (det-interval ∩ closed ball in matrix space)
    is compact. -/
theorem isCompact_sumZero_detInterval_product {n : ℕ}
    (R_phi R_A c C : ℝ) (hR : 0 ≤ R_phi) (A₀ : Matrix (Fin n) (Fin n) ℝ) :
    IsCompact (
      (Metric.closedBall (0 : Fin n → ℝ) R_phi ∩
       {phi : Fin n → ℝ | ∑ i, phi i = 0}) ×ˢ
      (Metric.closedBall A₀ R_A ∩
       {A : Matrix (Fin n) (Fin n) ℝ | c ≤ A.det ∧ A.det ≤ C})) := by
  apply isCompact_prod
  · exact sumZeroBall_compact R_phi hR
  · exact isCompact_detInterval_closedBall c C R_A A₀

end PallLean.Paper93.DeepMath.NFrame
