import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1Identity
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget5x5Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget6x6DetConcrete
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- Round-70 master summary: extends the round-69 conjunction with the
two new closed-form determinant identities at `n = 5` and `n = 6`,
namely `(compiledGadget α 5).det = α * (α + 5)^4` and
`(compiledGadget α 6).det = α * (α + 6)^5`. -/
theorem path_b_r70_master_summary :
    -- Identity universal
    (∀ (n : ℕ) (𝒥 : Finset (Finset (Fin n))),
       IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥) ∧
    -- n=1 collapse: compiledGadget 1 1 = identity
    (compiledGadget 1 1 = (1 : Matrix (Fin 1) (Fin 1) ℝ)) ∧
    -- n=2 non-trivial gauge
    (IsAmplituhedronGauge (compiledGadget (Real.sqrt 2 - 1) 2) (satFamily 2)) ∧
    (compiledGadget (Real.sqrt 2 - 1) 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    -- Universal existence: ∃ gauge witness for satFamily n at every n
    (∀ n : ℕ, ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A (satFamily n)) ∧
    -- Round-70 new: closed-form determinant at n=5
    (∀ α : ℝ, (compiledGadget α 5).det = α * (α + 5)^4) ∧
    -- Round-70 new: closed-form determinant at n=6
    (∀ α : ℝ, (compiledGadget α 6).det = α * (α + 6)^5) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n 𝒥 => identity_isAmplituhedronGauge_any 𝒥
  · exact compiledGadget_one_one_is_identity
  · exact compiledGadget_n2_isGauge_satFamily
  · exact compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)
  · exact fun n => ⟨1, identity_isAmplituhedronGauge_any (satFamily n)⟩
  · exact fun α => compiledGadget_5x5_det α
  · exact fun α => compiledGadget_6x6_det α

end PallLean.Paper93.DeepMath.PathB.Positroid
