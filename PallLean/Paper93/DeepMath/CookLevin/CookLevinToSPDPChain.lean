import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain
import PallLean.Paper93.DeepMath.CookLevin.CompiledTMPocketRank
import PallLean.Paper93.DeepMath.CookLevin.TableauEmbedRank

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank

/-- Summary statement: for α > 0 and tableau size ≥ 2, the rank of the compiled
    TM matrix is ≥ 1 (via the pocket decomposition chain). -/
theorem cookLevin_SPDP_chain
    (numStates numSymbols numTimesteps : ℕ) (α : ℝ)
    (hα : 0 < α)
    (hcard : 2 ≤ Fintype.card (TableauIndex numStates numSymbols numTimesteps)) :
    1 ≤ (compiledTMMatrix numStates numSymbols numTimesteps α).rank :=
  compiledTMMatrix_rank_pos numStates numSymbols numTimesteps α hα hcard

end PallLean.Paper93.DeepMath.CookLevin
