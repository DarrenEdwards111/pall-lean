import PallLean.Paper93.DeepMath.PathB.CompiledGadget2x2Det
import PallLean.Paper93.DeepMath.PathB.CompiledGadget3x3Det
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadget4x4DetExplicit
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- The det at α=1, n=2 is positive. -/
theorem det_n2_alpha_1_pos : 0 < (compiledGadget 1 2).det := by
  rw [compiledGadget_2x2_det]; norm_num

/-- The det at α=1, n=3 is positive. -/
theorem det_n3_alpha_1_pos : 0 < (compiledGadget 1 3).det := by
  rw [compiledGadget_3x3_det]; norm_num

/-- The det at α=1, n=4 is positive. -/
theorem det_n4_alpha_1_pos : 0 < (compiledGadget 1 4).det := by
  rw [compiledGadget_4x4_det]; norm_num

/-- The det at any α > 0 grows monotonically with α at small n. -/
theorem det_n2_monotonic (α β : ℝ) (h : 0 < α) (h2 : α ≤ β) :
    (compiledGadget α 2).det ≤ (compiledGadget β 2).det := by
  rw [compiledGadget_2x2_det, compiledGadget_2x2_det]
  nlinarith

end PallLean.Paper93.DeepMath.PathB.Positroid
