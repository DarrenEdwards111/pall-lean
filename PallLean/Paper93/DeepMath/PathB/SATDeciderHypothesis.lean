import PallLean.PaperFaithfulSeparation
import PallLean.Paper93.DeepMath.PathB.NFrameGodMoveSeam

namespace PallLean.Paper93.DeepMath.PathB

/-- A SAT decider is essentially `PeqNP_Paper` itself — a `DTM` deciding 3SAT in
    polynomial time. We re-export this for clarity in our Path B chain. -/
def SATDecider : Type := PaperFaithfulSeparation.PeqNP_Paper

/-- Conditional form only: a SAT decider yields contradiction under Bridge-A. -/
theorem SATDecider_implies_False_under_bridgeA
    (hBridgeA : NFrameGodMoveBridgeA) (decider : SATDecider) : False :=
  peqnp_false_of_nframe_godmove_bridgeA hBridgeA decider

end PallLean.Paper93.DeepMath.PathB
