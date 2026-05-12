import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.UnitMinorFinOne

namespace PallLean.Paper93.DeepMath.PathB

/-- For 1×1 matrices, gauge with empty family is trivially the identity matrix. -/
theorem fin_one_identity_gauge :
    IsAmplituhedronGauge (1 : Matrix (Fin 1) (Fin 1) ℝ) ∅ :=
  identity_isAmplituhedronGauge_empty

/-- For any n, the identity matrix is a gauge for the empty family. -/
theorem identity_n_gauge_empty {n : ℕ} :
    IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) ∅ :=
  identity_isAmplituhedronGauge_empty

end PallLean.Paper93.DeepMath.PathB
