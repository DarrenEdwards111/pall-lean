import PallLean.PaperFaithfulSeparation

namespace PallLean.Paper93.DeepMath.PathB

/-- A SAT decider is essentially `PeqNP_Paper` itself — a `DTM` deciding 3SAT in
    polynomial time. We re-export this for clarity in our Path B chain. -/
def SATDecider : Type := PaperFaithfulSeparation.PeqNP_Paper

/-- Existence: if there's a SAT decider with the polynomial-time bounds, the paper's
    `P_ne_NP_unconditional` rejects this (i.e., produces False). -/
theorem SATDecider_implies_False (decider : SATDecider) : False :=
  PaperFaithfulSeparation.P_ne_NP_unconditional decider

end PallLean.Paper93.DeepMath.PathB
