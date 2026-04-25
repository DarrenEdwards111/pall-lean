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
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem all_rounds_r62_final_kernel :
    (∀ n : ℕ, IsPrincipalTNN (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    (∀ (n : ℕ) (𝒥 : Finset (Finset (Fin n))),
       IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥) ∧
    (∀ a b c d e f g h : ℝ,
       (a*f - b*e) * (c*h - d*g) - (a*g - c*e) * (b*h - d*f) + (a*h - d*e) * (b*g - c*f) = 0) ∧
    (∀ (α : ℝ) (n : ℕ), 2 ≤ n → compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → (compiledGadget α n).PosDef) ∧
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → 0 < (compiledGadget α n).det) ∧
    (compiledGadget 1 1 = (1 : Matrix (Fin 1) (Fin 1) ℝ) ∧
     IsAmplituhedronGauge (compiledGadget 1 1) (satFamily 1)) ∧
    (IsAmplituhedronGauge (compiledGadget (Real.sqrt 2 - 1) 2) (satFamily 2) ∧
     compiledGadget (Real.sqrt 2 - 1) 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ (m n : ℕ) (T : SATDeciderTableau m n),
       ∅ ∈ T.extractedFamily ∧ (Finset.univ : Finset (Fin n)) ∈ T.extractedFamily) ∧
    (∀ (m : ℕ) (T : SATDeciderTableau m 2),
       ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
         IsAmplituhedronGauge A (satFamily 2) ∧
         A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ n : ℕ, ∃ A : Matrix (Fin n) (Fin n) ℝ, IsAmplituhedronGauge A (satFamily n)) ∧
    (∃ A : Matrix (Fin 4) (Fin 4) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 4) (Fin 4) ℝ)) ∧
    (∃ A : Matrix (Fin 5) (Fin 5) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 5) (Fin 5) ℝ)) ∧
    (∃ A : Matrix (Fin 6) (Fin 6) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 6) (Fin 6) ℝ)) ∧
    (∃ A : Matrix (Fin 7) (Fin 7) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 7) (Fin 7) ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact identity_isPrincipalTNN
  · exact fun n 𝒥 => identity_isAmplituhedronGauge_any 𝒥
  · exact plucker_relation_2x4
  · intros α n hn; exact compiledGadget_ne_identity α n hn
  · exact compiledGadget_posDef
  · intros α n hα hn; exact Matrix.PosDef.det_pos (compiledGadget_posDef α n hα hn)
  · exact ⟨compiledGadget_one_one_is_identity, compiledGadget_one_one_isGauge_satFamily⟩
  · exact ⟨compiledGadget_n2_isGauge_satFamily, compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩
  · exact fun m n T => ⟨T.extractedFamily_mem_empty, T.extractedFamily_mem_univ⟩
  · exact fun m _T =>
      ⟨compiledGadget (Real.sqrt 2 - 1) 2,
       compiledGadget_n2_isGauge_satFamily,
       compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩
  · exact fun n => ⟨1, identity_isAmplituhedronGauge_any (satFamily n)⟩
  · refine ⟨compiledGadget 1 4, ?_, ?_⟩
    · exact compiledGadget_posDef 1 4 one_pos (by norm_num)
    · exact compiledGadget_ne_identity 1 4 (by norm_num)
  · refine ⟨compiledGadget 1 5, ?_, ?_⟩
    · exact compiledGadget_posDef 1 5 one_pos (by norm_num)
    · exact compiledGadget_ne_identity 1 5 (by norm_num)
  · refine ⟨compiledGadget 1 6, ?_, ?_⟩
    · exact compiledGadget_posDef 1 6 one_pos (by norm_num)
    · exact compiledGadget_ne_identity 1 6 (by norm_num)
  · refine ⟨compiledGadget 1 7, ?_, ?_⟩
    · exact compiledGadget_posDef 1 7 one_pos (by norm_num)
    · exact compiledGadget_ne_identity 1 7 (by norm_num)

end PallLean.Paper93.DeepMath.PathB.Positroid
