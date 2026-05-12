import PallLean.Paper93.DeepMath.CookLevin.NTM
import PallLean.Paper93.DeepMath.CookLevin.CompiledTM
import PallLean.Paper93.DeepMath.CookLevin.TableauEmbedRank

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.CookLevin

/-- A SAT decider compilation structure: the tableau parameters (numStates × numSymbols × numTimesteps)
    and a coupling α giving rise to a compiled matrix. -/
structure SATCompilationParams where
  numStates : ℕ
  numSymbols : ℕ
  numTimesteps : ℕ
  α : ℝ
  hα : 0 < α
  hcard : 2 ≤ Fintype.card (TableauIndex numStates numSymbols numTimesteps)

/-- Given SAT compilation params, the compiled matrix has rank ≥ 1. -/
theorem SAT_compiled_rank_pos (p : SATCompilationParams) :
    1 ≤ (compiledTMMatrix p.numStates p.numSymbols p.numTimesteps p.α).rank :=
  compiledTMMatrix_rank_pos p.numStates p.numSymbols p.numTimesteps p.α p.hα p.hcard

end PallLean.Paper93.DeepMath.PathB
