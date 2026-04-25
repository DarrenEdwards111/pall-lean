import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- Cumulative summary: gauge witnesses exist universally for satFamily. -/
theorem cumulative_summary_r70_universal_gauge :
    ∀ n : ℕ, ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A (satFamily n) :=
  fun n => ⟨1, identity_isAmplituhedronGauge_any (satFamily n)⟩

/-- Cumulative summary: identity matrices gauge any family at any n. -/
theorem cumulative_summary_r70_identity_gauge :
    ∀ (n : ℕ) (𝒥 : Finset (Finset (Fin n))),
      IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥 :=
  fun n 𝒥 => identity_isAmplituhedronGauge_any 𝒥

end PallLean.Paper93.DeepMath.PathB.Positroid
