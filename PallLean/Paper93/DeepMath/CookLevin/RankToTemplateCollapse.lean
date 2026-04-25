import PallLean.Step4Compiler
import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB
open Step4Compiler

/-- Hypothesis-form: Given a hypothetical reduction from compiled-gadget rank ≥ κ to template-collapse,
    we can apply it to our proven rank chain. -/
theorem rank_chain_via_template_collapse
    (template_collapse_from_rank :
      (∀ α κ n : ℕ, 0 < (α : ℝ) → 2 ≤ n → κ ≤ (pocketFamily (α : ℝ) κ n).rank) → P ≠ NP) :
    P ≠ NP :=
  template_collapse_from_rank
    (fun α κ n hα hn => theorem_207_rank_chain (α : ℝ) κ n hα hn)

end PallLean.Paper93.DeepMath.CookLevin
