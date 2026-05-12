import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.NFrame.IdentityPosDef

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- For PosDef A and the empty family, A is trivially a gauge (vacuously satisfies
    the principal-minor condition). -/
theorem posDef_isGauge_at_empty {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    IsAmplituhedronGauge A ∅ := by
  refine ⟨hA, ?_⟩
  intros J hJ
  exact absurd hJ (Finset.notMem_empty J)

end PallLean.Paper93.DeepMath.PathB
