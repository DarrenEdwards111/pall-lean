import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_15_diag (α : ℝ) (i : Fin 15) :
    compiledGadget α 15 i i = α + 14 := by rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_16_diag (α : ℝ) (i : Fin 16) :
    compiledGadget α 16 i i = α + 15 := by rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_17_diag (α : ℝ) (i : Fin 17) :
    compiledGadget α 17 i i = α + 16 := by rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_18_diag (α : ℝ) (i : Fin 18) :
    compiledGadget α 18 i i = α + 17 := by rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_19_diag (α : ℝ) (i : Fin 19) :
    compiledGadget α 19 i i = α + 18 := by rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_20_diag (α : ℝ) (i : Fin 20) :
    compiledGadget α 20 i i = α + 19 := by rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_15_trace (α : ℝ) :
    (compiledGadget α 15).trace = 15 * α + 210 := by rw [compiledGadget_trace_formula]; ring

theorem compiledGadget_20_trace (α : ℝ) :
    (compiledGadget α 20).trace = 20 * α + 380 := by rw [compiledGadget_trace_formula]; ring

end PallLean.Paper93.DeepMath.PathB.Positroid
