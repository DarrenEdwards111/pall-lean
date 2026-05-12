import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_5x5_diag (α : ℝ) (i : Fin 5) :
    compiledGadget α 5 i i = α + 4 := by
  rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_5x5_trace (α : ℝ) :
    (compiledGadget α 5).trace = 5 * α + 20 := by
  rw [compiledGadget_trace_formula]; ring

theorem compiledGadget_6x6_diag (α : ℝ) (i : Fin 6) :
    compiledGadget α 6 i i = α + 5 := by
  rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_6x6_trace (α : ℝ) :
    (compiledGadget α 6).trace = 6 * α + 30 := by
  rw [compiledGadget_trace_formula]; ring

end PallLean.Paper93.DeepMath.PathB.Positroid
