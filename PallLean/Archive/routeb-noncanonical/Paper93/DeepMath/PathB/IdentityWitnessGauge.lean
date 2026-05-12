import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- The identity matrix witnesses the existence of an amplituhedron gauge — for any n and any family
    𝒥 of subsets. This is the strongest existence statement we can prove kernel-only. -/
theorem identity_witness_kernel_only {n : ℕ} (𝒥 : Finset (Finset (Fin n))) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A 𝒥 ∧ A = 1 :=
  ⟨1, identity_isAmplituhedronGauge_any 𝒥, rfl⟩

end PallLean.Paper93.DeepMath.PathB
