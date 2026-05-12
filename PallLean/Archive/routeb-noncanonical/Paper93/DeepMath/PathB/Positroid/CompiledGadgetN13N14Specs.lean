import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_13x13_diag (α : ℝ) (i : Fin 13) :
    compiledGadget α 13 i i = α + 12 := by
  rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_13x13_trace (α : ℝ) :
    (compiledGadget α 13).trace = 13 * α + 156 := by
  rw [compiledGadget_trace_formula]; ring

theorem compiledGadget_14x14_diag (α : ℝ) (i : Fin 14) :
    compiledGadget α 14 i i = α + 13 := by
  rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_14x14_trace (α : ℝ) :
    (compiledGadget α 14).trace = 14 * α + 182 := by
  rw [compiledGadget_trace_formula]; ring

end PallLean.Paper93.DeepMath.PathB.Positroid
