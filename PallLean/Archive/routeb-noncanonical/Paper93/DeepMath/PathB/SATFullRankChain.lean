import PallLean.Paper93.DeepMath.PathB.SATCompilationStructure
import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain
import PallLean.Paper93.DeepMath.BridgeB.PocketFamily

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.CookLevin
open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- For SAT compilation params and any κ, the κ-pocket family of the compiled-gadget at the
    decider's tableau-size has rank ≥ κ. -/
theorem SAT_pocket_rank_chain (p : SATCompilationParams) (κ : ℕ)
    (hn : 2 ≤ p.numStates * p.numSymbols * p.numTimesteps) :
    κ ≤ (pocketFamily p.α κ (p.numStates * p.numSymbols * p.numTimesteps)).rank :=
  theorem_207_rank_chain p.α κ (p.numStates * p.numSymbols * p.numTimesteps) p.hα hn

end PallLean.Paper93.DeepMath.PathB
