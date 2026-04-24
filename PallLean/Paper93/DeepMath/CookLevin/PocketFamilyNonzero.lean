import PallLean.Paper93.DeepMath.BridgeB.PocketFamily
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetNonzero

namespace PallLean.Paper93.DeepMath.CookLevin

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB

/-- Pocket family is nonzero when each block is nonzero (α > 0, n ≥ 2) and κ ≥ 1. -/
theorem pocketFamily_ne_zero (α : ℝ) (κ n : ℕ) (hκ : 1 ≤ κ) (hα : 0 < α) (hn : 2 ≤ n) :
    pocketFamily α κ n ≠ 0 := by
  intro h
  apply compiledGadget_ne_zero α n hα hn
  unfold pocketFamily at h
  -- blockDiagonal M = 0 ⇒ M i = 0 for every i (in particular i = 0)
  -- Use Matrix.blockDiagonal_apply_eq + an appropriate index to extract.
  have key : ∀ (i : Fin κ) (p q : Fin n), (compiledGadget α n) p q = 0 := by
    intro i p q
    have hpq := congrArg (fun M => M (p, i) (q, i)) h
    simp [Matrix.blockDiagonal_apply_eq] at hpq
    -- hpq : (compiledGadget α n) p q = 0
    exact hpq
  ext p q
  exact key ⟨0, hκ⟩ p q

end PallLean.Paper93.DeepMath.CookLevin
