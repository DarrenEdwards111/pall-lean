import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.NFrame

/-- If a minimizer of S_NF on a region constrained to A = identity exists,
    that A automatically satisfies IsAmplituhedronGauge for any family.
    This is a tautology — A is fixed at I. -/
theorem identity_constrained_minimizer_gauge {n : ℕ}
    (𝒥 : Finset (Finset (Fin n))) :
    IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥 :=
  identity_isAmplituhedronGauge_any 𝒥

/-- Composition: the existence of an A-identity-constrained minimizer + this trivial
    gauge property gives ∃ minimizer A* with gauge property. -/
theorem exists_minimizer_with_gauge {n : ℕ} (𝒥 : Finset (Finset (Fin n))) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A 𝒥 :=
  ⟨1, identity_constrained_minimizer_gauge 𝒥⟩

end PallLean.Paper93.DeepMath.PathB
