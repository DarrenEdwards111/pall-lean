import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN1Det
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.Tactic.NormNum

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_1_1_det_eq_one : (compiledGadget 1 1).det = 1 := by
  rw [compiledGadget_1x1_det]

theorem compiledGadget_1_2_det_eq_3 : (compiledGadget 1 2).det = 3 := by
  rw [compiledGadget_2x2_det]; norm_num

theorem compiledGadget_1_3_det_eq_16 : (compiledGadget 1 3).det = 16 := by
  rw [compiledGadget_3x3_det]; norm_num

theorem compiledGadget_1_4_det_eq_125 : (compiledGadget 1 4).det = 125 :=
  compiledGadget_4x4_det_at_one

end PallLean.Paper93.DeepMath.PathB.Positroid
