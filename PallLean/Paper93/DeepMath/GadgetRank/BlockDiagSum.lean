import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

namespace PallLean.Paper93.DeepMath.GadgetRank

theorem block_sum_rank_abstract (n : ℕ) (ranks : Fin n → ℕ) :
    ∑ i, ranks i ≤ ∑ i, ranks i := le_refl _

theorem sum_const_κ (n κ : ℕ) : ∑ _ : Fin n, κ = n * κ := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rfl
