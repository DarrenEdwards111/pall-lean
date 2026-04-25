import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- For any n and any family 𝒥, there EXISTS a matrix A satisfying IsAmplituhedronGauge —
    namely, the identity matrix. This is a structural-existence statement, kernel-only. -/
theorem exists_amplituhedron_gauge {n : ℕ} (𝒥 : Finset (Finset (Fin n))) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A 𝒥 :=
  ⟨1, identity_isAmplituhedronGauge_any 𝒥⟩

/-- Concrete witness: identity matrix. -/
theorem identity_witnesses_gauge {n : ℕ} (𝒥 : Finset (Finset (Fin n))) :
    IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥 :=
  identity_isAmplituhedronGauge_any 𝒥

end PallLean.Paper93.DeepMath.PathB
