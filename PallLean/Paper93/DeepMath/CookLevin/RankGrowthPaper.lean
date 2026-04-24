import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain
import PallLean.Paper93.DeepMath.CookLevin.CompiledTMPocketRank
import PallLean.Paper93.DeepMath.CookLevin.CompiledTM

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- Headline structural theorem: κ-pocket Cook-Levin rank grows at least linearly with κ. -/
theorem cook_levin_rank_lower_bound_linear (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    ∀ κ, κ ≤ (pocketFamily α κ n).rank := by
  intros κ
  exact theorem_207_rank_chain α κ n hα hn

/-- Growth quantifier: for any target M, we can pick κ ≥ M to get rank ≥ M. -/
theorem cook_levin_rank_unbounded_as_kappa_grows (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    ∀ M : ℕ, ∃ κ : ℕ, M ≤ (pocketFamily α κ n).rank := by
  intro M
  exact ⟨M, theorem_207_rank_chain α M n hα hn⟩

end PallLean.Paper93.DeepMath.CookLevin
