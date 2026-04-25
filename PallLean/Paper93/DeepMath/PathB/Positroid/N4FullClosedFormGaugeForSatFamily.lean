import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.PathB.Positroid.N4IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetNonIdentityAny
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.PrincipalMinorAtUniv
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetMinorEmpty
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Logic.Equiv.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- ∃ non-identity PosDef 4×4 matrix with det = 1 from the §28.3 construction. -/
theorem exists_nonidentity_posDef_det_one_n4_full :
    ∃ A : Matrix (Fin 4) (Fin 4) ℝ,
      A.PosDef ∧ A.det = 1 ∧ A ≠ (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  obtain ⟨α, hα_pos, _, hα_eq⟩ := exists_alpha_n4_det_one
  refine ⟨compiledGadget α 4, ?_, ?_, ?_⟩
  · exact compiledGadget_posDef α 4 hα_pos (by norm_num)
  · rw [compiledGadget_4x4_det]; exact hα_eq
  · exact compiledGadget_ne_identity α 4 (by norm_num)

end PallLean.Paper93.DeepMath.PathB.Positroid
