import PallLean.Paper93.DeepMath.NFrame.PosDefDetBall
import PallLean.Paper93.DeepMath.NFrame.IdentityPosDef

namespace PallLean.Paper93.DeepMath.NFrame

open scoped Matrix.Norms.Elementwise

/-- A specific compact subset of PosDef-like matrices around the identity:
    `{A : 1/2 ≤ det A ≤ 2 ∧ ‖A - I‖ ≤ 1/2}`. Not all of PosDef, but a concrete compact neighborhood. -/
def concretePosDefRegion (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  Metric.closedBall (1 : Matrix (Fin n) (Fin n) ℝ) (1/2) ∩
  {A | (1/2 : ℝ) ≤ A.det ∧ A.det ≤ 2}

theorem concretePosDefRegion_isCompact (n : ℕ) : IsCompact (concretePosDefRegion n) :=
  isCompact_detInterval_closedBall (1/2) 2 (1/2) (1 : Matrix (Fin n) (Fin n) ℝ)

end PallLean.Paper93.DeepMath.NFrame
