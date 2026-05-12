import PallLean.Paper93.DeepMath.CookLevin.CompiledTM
import PallLean.Paper93.DeepMath.CookLevin.CookLevinGadget
import PallLean.Paper93.DeepMath.CookLevin.TableauEmbedRank

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.CookLevin

/-- The Cook-Levin compiled gadget acts as the bridge from a SAT decider's tableau
    to a matrix structure. For α > 0 and tableau size ≥ 2, the compiled TM matrix is
    nonzero, hence has rank ≥ 1. -/
theorem compiledTM_for_SAT_nonzero
    (numStates numSymbols numTimesteps : ℕ) (α : ℝ)
    (hα : 0 < α)
    (hcard : 2 ≤ Fintype.card (TableauIndex numStates numSymbols numTimesteps)) :
    1 ≤ (compiledTMMatrix numStates numSymbols numTimesteps α).rank :=
  compiledTMMatrix_rank_pos numStates numSymbols numTimesteps α hα hcard

end PallLean.Paper93.DeepMath.PathB
