import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2NotIdentity
import PallLean.Paper93.DeepMath.PathB.Sqrt2MinusOnePos
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- Round-62 deep progress: extends earlier rounds with n=6, n=7 non-identity PosDef matrices. -/
theorem round_62_deep_progress :
    (∀ n : ℕ, IsPrincipalTNN (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    (∀ (n : ℕ) (𝒥 : Finset (Finset (Fin n))),
       IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥) ∧
    (∀ (α : ℝ) (n : ℕ), 2 ≤ n → compiledGadget α n ≠ (1 : Matrix (Fin n) (Fin n) ℝ)) ∧
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → (compiledGadget α n).PosDef) ∧
    (IsAmplituhedronGauge (compiledGadget (Real.sqrt 2 - 1) 2) (satFamily 2) ∧
     compiledGadget (Real.sqrt 2 - 1) 2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∃ A : Matrix (Fin 6) (Fin 6) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 6) (Fin 6) ℝ)) ∧
    (∃ A : Matrix (Fin 7) (Fin 7) ℝ, A.PosDef ∧ A ≠ (1 : Matrix (Fin 7) (Fin 7) ℝ)) ∧
    (∀ (α : ℝ) (n : ℕ), 0 < α → 1 ≤ n → 0 < (compiledGadget α n).det) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact identity_isPrincipalTNN
  · exact fun n 𝒥 => identity_isAmplituhedronGauge_any 𝒥
  · intros α n hn; exact compiledGadget_ne_identity α n hn
  · exact compiledGadget_posDef
  · exact ⟨compiledGadget_n2_isGauge_satFamily, compiledGadget_2x2_ne_identity (Real.sqrt 2 - 1)⟩
  · refine ⟨compiledGadget 1 6, ?_, ?_⟩
    · exact compiledGadget_posDef 1 6 one_pos (by norm_num)
    · exact compiledGadget_ne_identity 1 6 (by norm_num)
  · refine ⟨compiledGadget 1 7, ?_, ?_⟩
    · exact compiledGadget_posDef 1 7 one_pos (by norm_num)
    · exact compiledGadget_ne_identity 1 7 (by norm_num)
  · intros α n hα hn
    exact Matrix.PosDef.det_pos (compiledGadget_posDef α n hα hn)

end PallLean.Paper93.DeepMath.PathB.Positroid
