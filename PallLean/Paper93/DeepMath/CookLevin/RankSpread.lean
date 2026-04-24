import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- For any `k`, taking κ = k makes the pocket family rank ≥ k. Hence the rank is
    unbounded above as κ → ∞. -/
theorem pocketFamily_rank_unbounded (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) (k : ℕ) :
    ∃ κ : ℕ, k ≤ (pocketFamily α κ n).rank :=
  ⟨k, theorem_207_rank_chain α k n hα hn⟩

/-- For κ ≥ M, rank ≥ M. -/
theorem pocketFamily_rank_ge_of_κ_ge (α : ℝ) (n M : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    ∀ κ ≥ M, M ≤ (pocketFamily α κ n).rank := by
  intros κ hκ
  have h := theorem_207_rank_chain α κ n hα hn
  omega

end PallLean.Paper93.DeepMath.CookLevin
