import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain
import PallLean.Paper93.DeepMath.CookLevin.PaperPNotNPHypothesis
import PallLean.Step4Compiler

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB
open Step4Compiler

/-- Paper §28.3 / §40 Theorem 207 (final, hypothesis-form): given any bridge from the
    Lean-side rank chain (which is proved unconditionally) to the P ≠ NP statement,
    we get P ≠ NP. -/
theorem paper_final_P_ne_NP_via_rank
    (bridge : (∀ α κ n : ℕ, 0 < (α : ℝ) → 2 ≤ n →
                κ ≤ (pocketFamily (α : ℝ) κ n).rank) → P ≠ NP) :
    P ≠ NP :=
  bridge (fun α κ n hα hn => theorem_207_rank_chain (α : ℝ) κ n hα hn)

end PallLean.Paper93.DeepMath.CookLevin
