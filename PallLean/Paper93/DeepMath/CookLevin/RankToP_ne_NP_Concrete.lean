import PallLean.PaperFaithfulSeparation
import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain
import PallLean.Step4Compiler

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.BridgeB

/-- Concrete bridge attempt: given any hypothesis-form theorem in PaperFaithfulSeparation
    that consumes our rank chain shape and produces P ≠ NP, the rank chain is unconditional
    so the result follows. -/
theorem rank_to_P_ne_NP_via_paper_faithful
    (bridge : (∀ α κ n : ℕ, 0 < (α : ℝ) → 2 ≤ n →
                 κ ≤ (pocketFamily (α : ℝ) κ n).rank) →
              Step4Compiler.P ≠ Step4Compiler.NP) :
    Step4Compiler.P ≠ Step4Compiler.NP :=
  bridge (fun α κ n hα hn => theorem_207_rank_chain (α : ℝ) κ n hα hn)

end PallLean.Paper93.DeepMath.CookLevin
