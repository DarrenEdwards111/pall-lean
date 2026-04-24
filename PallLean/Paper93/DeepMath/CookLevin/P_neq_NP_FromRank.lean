import PallLean.Paper93.DeepMath.CookLevin.PaperPNotNPHypothesis
import PallLean.Step4Compiler

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB
open Step4Compiler

/-- Re-export of the abstract hypothesis-form: given the rank chain (proved as `paper_theorem_207`),
    and given any bridge `rank_to_P_neq_NP` from rank chain to P ≠ NP, conclude P ≠ NP. -/
theorem P_neq_NP_from_rank_chain
    (rank_to_P_neq_NP : (∀ α κ n : ℕ, 0 < (α : ℝ) → 2 ≤ n →
                          κ ≤ (pocketFamily (α : ℝ) κ n).rank) → P ≠ NP)
    (rank_chain : ∀ α κ n : ℕ, 0 < (α : ℝ) → 2 ≤ n →
                    κ ≤ (pocketFamily (α : ℝ) κ n).rank) :
    P ≠ NP :=
  rank_to_P_neq_NP rank_chain

end PallLean.Paper93.DeepMath.CookLevin
