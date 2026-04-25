import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-! # Path B: N=1 Minimizer-Is-Gauge

For the N=1 case, the identity matrix coincides with the trivial gauge, so the
"minimizer is gauge" step is unconditional. This file records that kernel-only
identification. -/

/-- N=1 case: the identity matrix satisfies the amplituhedron gauge property for
    any family 𝒥 of index subsets. -/
theorem fin_one_identity_isAmplituhedronGauge_any
    (𝒥 : Finset (Finset (Fin 1))) :
    IsAmplituhedronGauge (1 : Matrix (Fin 1) (Fin 1) ℝ) 𝒥 :=
  identity_isAmplituhedronGauge_any 𝒥

/-- N=1 case: for any family, there exists a gauge witness -- namely, identity. -/
theorem fin_one_exists_amplituhedron_gauge
    (𝒥 : Finset (Finset (Fin 1))) :
    ∃ A : Matrix (Fin 1) (Fin 1) ℝ, IsAmplituhedronGauge A 𝒥 :=
  ⟨1, fin_one_identity_isAmplituhedronGauge_any 𝒥⟩

/-- N=1 "minimizer is gauge" packaging: any matrix equal to the identity is a
    gauge for any family. This captures the trivial minimizer = identity case. -/
theorem fin_one_min_is_gauge
    (A_star : Matrix (Fin 1) (Fin 1) ℝ)
    (𝒥 : Finset (Finset (Fin 1)))
    (hA : A_star = 1) :
    IsAmplituhedronGauge A_star 𝒥 := by
  rw [hA]
  exact fin_one_identity_isAmplituhedronGauge_any 𝒥

end PallLean.Paper93.DeepMath.PathB
