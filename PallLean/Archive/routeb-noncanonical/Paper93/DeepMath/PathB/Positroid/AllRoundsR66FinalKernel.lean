import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import PallLean.Paper93.DeepMath.PathB.Positroid.PluckerRelation2x4
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1Identity
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem all_rounds_r66_final_kernel :
    (∀ n : ℕ, IsPrincipalTNN (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    (∀ (n : ℕ) (𝒥 : Finset (Finset (Fin n))),
       IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥) ∧
    (∀ (α : ℝ) (n : ℕ), 2 ≤ n → compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → (compiledGadget α n).PosDef) ∧
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → 0 < (compiledGadget α n).det) ∧
    (compiledGadget 1 1 = (1 : Matrix (Fin 1) (Fin 1) ℝ) ∧
     IsAmplituhedronGauge (compiledGadget 1 1) (satFamily 1)) ∧
    (IsAmplituhedronGauge (compiledGadget (Real.sqrt 2 - 1) 2) (satFamily 2) ∧
     compiledGadget (Real.sqrt 2 - 1) 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ α : ℝ, (compiledGadget α 2).det = α * (α + 2)) ∧
    (∀ α : ℝ, (compiledGadget α 3).det = α * (α + 3)^2) ∧
    (∀ α : ℝ, (compiledGadget α 4).det = α * (α + 4)^3) ∧
    (∀ n : ℕ, ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A (satFamily n)) ∧
    (∃ A : Matrix (Fin 11) (Fin 11) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 11) (Fin 11) ℝ)) ∧
    (∃ A : Matrix (Fin 12) (Fin 12) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 12) (Fin 12) ℝ)) ∧
    (∃ A : Matrix (Fin 13) (Fin 13) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 13) (Fin 13) ℝ)) ∧
    (∃ A : Matrix (Fin 14) (Fin 14) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 14) (Fin 14) ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact identity_isPrincipalTNN
  · exact fun n 𝒥 => identity_isAmplituhedronGauge_any 𝒥
  · intros α n hn; exact compiledGadget_ne_identity α n hn
  · exact compiledGadget_posDef
  · intros α n hα hn; exact Matrix.PosDef.det_pos (compiledGadget_posDef α n hα hn)
  · exact ⟨compiledGadget_one_one_is_identity, compiledGadget_one_one_isGauge_satFamily⟩
  · exact ⟨compiledGadget_n2_isGauge_satFamily, compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩
  · exact compiledGadget_2x2_det
  · exact compiledGadget_3x3_det
  · exact compiledGadget_4x4_det
  · exact fun n => ⟨1, identity_isAmplituhedronGauge_any (satFamily n)⟩
  · exact ⟨compiledGadget 1 11, compiledGadget_posDef 1 11 one_pos (by norm_num),
           compiledGadget_ne_identity 1 11 (by norm_num)⟩
  · exact ⟨compiledGadget 1 12, compiledGadget_posDef 1 12 one_pos (by norm_num),
           compiledGadget_ne_identity 1 12 (by norm_num)⟩
  · exact ⟨compiledGadget 1 13, compiledGadget_posDef 1 13 one_pos (by norm_num),
           compiledGadget_ne_identity 1 13 (by norm_num)⟩
  · exact ⟨compiledGadget 1 14, compiledGadget_posDef 1 14 one_pos (by norm_num),
           compiledGadget_ne_identity 1 14 (by norm_num)⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
