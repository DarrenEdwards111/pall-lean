import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_200x200_diag (α : ℝ) (i : Fin 200) :
    compiledGadget α 200 i i = α + 199 := by
  rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_200x200_trace (α : ℝ) :
    (compiledGadget α 200).trace = 200 * α + 200 * 199 := by
  rw [compiledGadget_trace_formula]; ring

theorem compiledGadget_500x500_diag (α : ℝ) (i : Fin 500) :
    compiledGadget α 500 i i = α + 499 := by
  rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_500x500_trace (α : ℝ) :
    (compiledGadget α 500).trace = 500 * α + 500 * 499 := by
  rw [compiledGadget_trace_formula]; ring

theorem compiledGadget_1000x1000_diag (α : ℝ) (i : Fin 1000) :
    compiledGadget α 1000 i i = α + 999 := by
  rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_1000x1000_trace (α : ℝ) :
    (compiledGadget α 1000).trace = 1000 * α + 1000 * 999 := by
  rw [compiledGadget_trace_formula]; ring

end PallLean.Paper93.DeepMath.PathB.Positroid
