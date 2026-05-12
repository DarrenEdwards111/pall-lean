import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_7x7_diag (α : ℝ) (i : Fin 7) :
    compiledGadget α 7 i i = α + 6 := by
  rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_7x7_trace (α : ℝ) :
    (compiledGadget α 7).trace = 7 * α + 42 := by
  rw [compiledGadget_trace_formula]; ring

theorem compiledGadget_8x8_diag (α : ℝ) (i : Fin 8) :
    compiledGadget α 8 i i = α + 7 := by
  rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_8x8_trace (α : ℝ) :
    (compiledGadget α 8).trace = 8 * α + 56 := by
  rw [compiledGadget_trace_formula]; ring

theorem compiledGadget_12x12_diag (α : ℝ) (i : Fin 12) :
    compiledGadget α 12 i i = α + 11 := by
  rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_12x12_trace (α : ℝ) :
    (compiledGadget α 12).trace = 12 * α + 132 := by
  rw [compiledGadget_trace_formula]; ring

theorem compiledGadget_14x14_diag (α : ℝ) (i : Fin 14) :
    compiledGadget α 14 i i = α + 13 := by
  rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_14x14_trace (α : ℝ) :
    (compiledGadget α 14).trace = 14 * α + 182 := by
  rw [compiledGadget_trace_formula]; ring

end PallLean.Paper93.DeepMath.PathB.Positroid
