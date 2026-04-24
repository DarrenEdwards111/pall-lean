import PallLean.Paper93.DeepMath.CookLevin.Theorem207Chain
import PallLean.Paper93.DeepMath.CookLevin.CompiledTM

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- For κ pockets growing polynomially with input size, the pocket family rank also grows
    polynomially. (This is the structural form of "rank ≥ poly(input)" needed for the
    paper's NP-hardness rank-lower-bound reduction.) -/
theorem pocketFamily_rank_grows_polynomially (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    ∀ p : ℕ → ℕ, ∀ N : ℕ, p N ≤ (pocketFamily α (p N) n).rank :=
  fun p N => theorem_207_rank_chain α (p N) n hα hn

/-- Existence: for any polynomial p, the rank ≥ p(N) is achievable by choosing κ = p(N). -/
theorem pocketFamily_rank_achieves_polynomial (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 2 ≤ n) :
    ∀ p : ℕ → ℕ, ∀ N : ℕ, ∃ κ, p N ≤ (pocketFamily α κ n).rank :=
  fun p N => ⟨p N, theorem_207_rank_chain α (p N) n hα hn⟩

end PallLean.Paper93.DeepMath.CookLevin
