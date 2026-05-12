import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB

/-- Scaled-all-ones tableau (entries = c for c ≥ 0). -/
def SATDeciderTableau.scaledAllOnes (m n : ℕ) (c : ℝ) (hc : 0 ≤ c) : SATDeciderTableau m n where
  tableau := fun _ _ => c
  row_sum_nonneg := by
    intro i
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    exact mul_nonneg (Nat.cast_nonneg n) hc

theorem scaledAllOnes_zero_eq_zero (m n : ℕ) :
    (SATDeciderTableau.scaledAllOnes m n 0 (le_refl 0)).tableau = 0 := by
  unfold SATDeciderTableau.scaledAllOnes
  ext i j
  rfl

theorem scaledAllOnes_one_eq_allOnes (m n : ℕ) :
    (SATDeciderTableau.scaledAllOnes m n 1 (by linarith)).tableau =
    (SATDeciderTableau.allOnes m n).tableau := by
  unfold SATDeciderTableau.scaledAllOnes SATDeciderTableau.allOnes
  rfl

end PallLean.Paper93.DeepMath.PathB.Positroid
