import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_9x9_diag (α : ℝ) (i : Fin 9) :
    compiledGadget α 9 i i = α + 8 := by
  rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_9x9_trace (α : ℝ) :
    (compiledGadget α 9).trace = 9 * α + 72 := by
  rw [compiledGadget_trace_formula]; ring

theorem compiledGadget_10x10_diag (α : ℝ) (i : Fin 10) :
    compiledGadget α 10 i i = α + 9 := by
  rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_10x10_trace (α : ℝ) :
    (compiledGadget α 10).trace = 10 * α + 90 := by
  rw [compiledGadget_trace_formula]; ring

end PallLean.Paper93.DeepMath.PathB.Positroid
