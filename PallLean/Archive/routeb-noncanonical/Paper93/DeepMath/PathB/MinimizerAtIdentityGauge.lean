import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- For the trivial minimizer (Φ = 0, A = I) of S_NF when restricted to where A is fixed at
    identity, A satisfies the gauge property. (Sanity check for the simplest case.) -/
theorem trivial_minimizer_is_gauge {n : ℕ} (𝒥 : Finset (Finset (Fin n))) :
    IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥 :=
  identity_isAmplituhedronGauge_any 𝒥

end PallLean.Paper93.DeepMath.PathB
