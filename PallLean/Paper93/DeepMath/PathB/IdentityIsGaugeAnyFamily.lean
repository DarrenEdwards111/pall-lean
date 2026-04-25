import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.NFrame.AdjugateOne

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- The identity matrix is a gauge for any family `𝒥`. This is the strongest statement
    of identity matrix's gauge property: for any J ⊆ Fin n and any e : Fin J.card ≃ {i // i ∈ J},
    the principal minor of identity at J is 1. -/
theorem identity_isAmplituhedronGauge_any {n : ℕ} (𝒥 : Finset (Finset (Fin n))) :
    IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥 := by
  refine ⟨Matrix.PosDef.one, ?_⟩
  intros J _hJ e
  -- The submatrix of identity at injective J via e is identity, det = 1
  have h_inj : Function.Injective (fun i => ((e i).1 : Fin n)) := by
    intros i j hij
    apply e.injective
    apply Subtype.ext
    exact hij
  rw [Matrix.submatrix_one _ h_inj, Matrix.det_one]

end PallLean.Paper93.DeepMath.PathB
