import PallLean.Paper93.DeepMath.PathB.SATDeciderHypothesis
import PallLean.Paper93.DeepMath.PathB.SATDeciderRankStatement

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- Contrapositive statement: if rank(pocketFamily α κ n) < κ for some choice of (α, κ, n),
    then we'd contradict `theorem_207_rank_chain`. So no such SAT decider exists.

    Used to detect any inconsistency: combining theorem_207_rank_chain with the SATDecider
    hypothesis form gives the impossibility. -/
theorem rank_lt_kappa_impossible (α : ℝ) (κ n : ℕ) (hα : 0 < α) (hn : 2 ≤ n)
    (h : (pocketFamily α κ n).rank < κ) :
    False := by
  have h_ge := rank_for_SAT_decider_compilation α κ n hα hn
  exact absurd h_ge (not_le.mpr h)

end PallLean.Paper93.DeepMath.PathB
