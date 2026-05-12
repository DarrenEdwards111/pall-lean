import PallLean.Paper93.DeepMath.PathB.MinimizerToGauge
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- SPECIAL CASE: when the minimizer (Φ*, A*) has A* = identity, it is automatically a gauge
    for any family. (Paper §28.3 minimizer = gauge identification holds in the trivial case.) -/
theorem special_minimizer_is_gauge_at_identity {n : ℕ}
    (Phi_star : Fin n → ℝ) (𝒥 : Finset (Finset (Fin n))) :
    IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥 :=
  identity_isAmplituhedronGauge_any 𝒥

end PallLean.Paper93.DeepMath.PathB
