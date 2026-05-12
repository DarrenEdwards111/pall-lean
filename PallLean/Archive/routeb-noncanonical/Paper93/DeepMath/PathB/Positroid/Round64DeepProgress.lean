import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem round_64_deep_progress :
    (∀ n : ℕ, IsPrincipalTNN (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    (∀ (n : ℕ) (𝒥 : Finset (Finset (Fin n))),
       IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥) ∧
    (∀ (α : ℝ) (n : ℕ), 2 ≤ n → compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → (compiledGadget α n).PosDef) ∧
    (IsAmplituhedronGauge (compiledGadget (Real.sqrt 2 - 1) 2) (satFamily 2) ∧
     compiledGadget (Real.sqrt 2 - 1) 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    -- Closed-form det at n=2,3,4
    (∀ α : ℝ, (compiledGadget α 2).det = α * (α + 2)) ∧
    (∀ α : ℝ, (compiledGadget α 3).det = α * (α + 3)^2) ∧
    (∀ α : ℝ, (compiledGadget α 4).det = α * (α + 4)^3) ∧
    -- New R64: existence of non-identity PosDef witnesses at n=8, 9, 10
    (∃ A : Matrix (Fin 8) (Fin 8) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 8) (Fin 8) ℝ)) ∧
    (∃ A : Matrix (Fin 9) (Fin 9) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 9) (Fin 9) ℝ)) ∧
    (∃ A : Matrix (Fin 10) (Fin 10) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 10) (Fin 10) ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact identity_isPrincipalTNN
  · exact fun n 𝒥 => identity_isAmplituhedronGauge_any 𝒥
  · intros α n hn; exact compiledGadget_ne_identity α n hn
  · exact compiledGadget_posDef
  · exact ⟨compiledGadget_n2_isGauge_satFamily, compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩
  · exact compiledGadget_2x2_det
  · exact compiledGadget_3x3_det
  · exact compiledGadget_4x4_det
  · refine ⟨compiledGadget 1 8, ?_, ?_⟩
    · exact compiledGadget_posDef 1 8 one_pos (by norm_num)
    · exact compiledGadget_ne_identity 1 8 (by norm_num)
  · refine ⟨compiledGadget 1 9, ?_, ?_⟩
    · exact compiledGadget_posDef 1 9 one_pos (by norm_num)
    · exact compiledGadget_ne_identity 1 9 (by norm_num)
  · refine ⟨compiledGadget 1 10, ?_, ?_⟩
    · exact compiledGadget_posDef 1 10 one_pos (by norm_num)
    · exact compiledGadget_ne_identity 1 10 (by norm_num)

end PallLean.Paper93.DeepMath.PathB.Positroid
