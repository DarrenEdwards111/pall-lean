import PallLean.Paper93.DeepMath.CookLevin.PaperFinalP_ne_NP
import PallLean.Step4Compiler

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB
open Step4Compiler

/-- Headline named theorem: paper §40 Theorem 207 — P ≠ NP follows from the rank chain
    plus an appropriate bridge, via the existing Step4Compiler infrastructure. -/
theorem paper_theorem_207_concludes_P_ne_NP_hypothesis
    (bridge : (∀ α κ n : ℕ, 0 < (α : ℝ) → 2 ≤ n →
                κ ≤ (pocketFamily (α : ℝ) κ n).rank) → P ≠ NP) :
    P ≠ NP :=
  paper_final_P_ne_NP_via_rank bridge

end PallLean.Paper93.DeepMath.CookLevin
