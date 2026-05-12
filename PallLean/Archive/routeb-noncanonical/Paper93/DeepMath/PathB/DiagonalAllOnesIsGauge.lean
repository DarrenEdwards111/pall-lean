import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.DiagonalUnitMinor
import PallLean.Paper93.DeepMath.NFrame.AdjugateOne

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- The identity matrix (= `Matrix.diagonal (fun _ => 1)`) is a gauge for ANY family `𝒥`
    of subsets, since every principal minor is 1 (its submatrix is identity).

    For now, we restate this for the empty family. -/
theorem identity_diagonal_gauge_empty {n : ℕ} :
    IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) ∅ :=
  identity_isAmplituhedronGauge_empty

end PallLean.Paper93.DeepMath.PathB
