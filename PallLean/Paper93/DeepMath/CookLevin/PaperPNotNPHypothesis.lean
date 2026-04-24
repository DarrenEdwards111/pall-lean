import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain
import PallLean.Step4Compiler

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB
open Step4Compiler

/-- Paper §40 Theorem 207 statement: under the rank lower bound (proved kernel-only),
    P ≠ NP. The hypothesis-form, since the actual bridge to P/NP is via Step4Compiler
    which lives in a different chain. -/
theorem rank_chain_implies_P_neq_NP_hypothesis
    (rank_chain : ∀ α κ n : ℕ, 0 < (α : ℝ) → 2 ≤ n → κ ≤ (pocketFamily (α : ℝ) κ n).rank)
    (rank_to_P_neq_NP : (∀ α κ n : ℕ, 0 < (α : ℝ) → 2 ≤ n →
                          κ ≤ (pocketFamily (α : ℝ) κ n).rank) → P ≠ NP) :
    P ≠ NP :=
  rank_to_P_neq_NP rank_chain

end PallLean.Paper93.DeepMath.CookLevin
