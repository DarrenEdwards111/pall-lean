import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

theorem compiledGadget_11x11_diag (α : ℝ) (i : Fin 11) :
    compiledGadget α 11 i i = α + 10 := by
  rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_11x11_trace (α : ℝ) :
    (compiledGadget α 11).trace = 11 * α + 110 := by
  rw [compiledGadget_trace_formula]; ring

theorem compiledGadget_12x12_diag (α : ℝ) (i : Fin 12) :
    compiledGadget α 12 i i = α + 11 := by
  rw [compiledGadget_diagonal]; norm_num

theorem compiledGadget_12x12_trace (α : ℝ) :
    (compiledGadget α 12).trace = 12 * α + 132 := by
  rw [compiledGadget_trace_formula]; ring

end PallLean.Paper93.DeepMath.PathB.Positroid
