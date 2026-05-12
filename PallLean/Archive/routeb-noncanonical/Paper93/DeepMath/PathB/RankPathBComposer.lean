import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain
import PallLean.Paper93.DeepMath.CookLevin.Final_P_ne_NP_Wrapper
import PallLean.PaperFaithfulSeparation

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB
open PallLean.Paper93.DeepMath.CookLevin

/-- Path B summary: the rank chain (proven kernel-only) plus the existing
    `PaperFaithfulSeparation.P_ne_NP_unconditional` chain together close
    the formalization at the cost of one upstream gauge axiom. -/
theorem path_B_full_chain : ∀ (_ : PaperFaithfulSeparation.PeqNP_Paper), False :=
  PallLean.Paper93.DeepMath.CookLevin.accesses_paper_unconditional

end PallLean.Paper93.DeepMath.PathB
