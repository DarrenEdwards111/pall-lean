import PallLean.Paper93.DeepMath.PathB.CompiledGadgetDiagonal
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetTraceFormula
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- Summary at n=25: diagonal = α + 24, trace = 25α + 600. -/
theorem compiledGadget_n25_summary (α : ℝ) :
    (∀ i : Fin 25, compiledGadget α 25 i i = α + 24) ∧
    (compiledGadget α 25).trace = 25 * α + 600 := by
  refine ⟨?_, ?_⟩
  · intro i; rw [compiledGadget_diagonal]; norm_num
  · rw [compiledGadget_trace_formula]; ring

/-- Summary at n=30. -/
theorem compiledGadget_n30_summary (α : ℝ) :
    (∀ i : Fin 30, compiledGadget α 30 i i = α + 29) ∧
    (compiledGadget α 30).trace = 30 * α + 870 := by
  refine ⟨?_, ?_⟩
  · intro i; rw [compiledGadget_diagonal]; norm_num
  · rw [compiledGadget_trace_formula]; ring

/-- Summary at n=50. -/
theorem compiledGadget_n50_summary (α : ℝ) :
    (∀ i : Fin 50, compiledGadget α 50 i i = α + 49) := by
  intro i; rw [compiledGadget_diagonal]; norm_num

/-- compiledGadget at α=1, n=50 is PosDef. -/
theorem compiledGadget_n50_posDef : (compiledGadget 1 50).PosDef :=
  compiledGadget_posDef 1 50 one_pos (by norm_num)

end PallLean.Paper93.DeepMath.PathB.Positroid
