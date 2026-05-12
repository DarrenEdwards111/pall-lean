import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_25_diag (α : ℝ) (i : Fin 25) :
    compiledGadget α 25 i i = α + 24 := by rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_30_diag (α : ℝ) (i : Fin 30) :
    compiledGadget α 30 i i = α + 29 := by rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_50_diag (α : ℝ) (i : Fin 50) :
    compiledGadget α 50 i i = α + 49 := by rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_25_trace (α : ℝ) :
    (compiledGadget α 25).trace = 25 * α + 600 := by rw [compiledGadget_trace_formula]; ring

theorem compiledGadget_30_trace (α : ℝ) :
    (compiledGadget α 30).trace = 30 * α + 870 := by rw [compiledGadget_trace_formula]; ring

theorem compiledGadget_50_trace (α : ℝ) :
    (compiledGadget α 50).trace = 50 * α + 2450 := by rw [compiledGadget_trace_formula]; ring

end PallLean.Paper93.DeepMath.PathB.Positroid
