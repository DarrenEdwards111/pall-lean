import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB

theorem zero_tableau_row_sum (m n : ℕ) (i : Fin m) :
    ∑ j, (SATDeciderTableau.zero m n).tableau i j = 0 := by
  unfold SATDeciderTableau.zero
  simp

theorem allOnes_tableau_row_sum (m n : ℕ) (i : Fin m) :
    ∑ j, (SATDeciderTableau.allOnes m n).tableau i j = (n : ℝ) := by
  unfold SATDeciderTableau.allOnes
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

theorem zero_tableau_row_sum_nonneg (m n : ℕ) (i : Fin m) :
    0 ≤ ∑ j, (SATDeciderTableau.zero m n).tableau i j := by
  rw [zero_tableau_row_sum]

theorem allOnes_tableau_row_sum_nonneg (m n : ℕ) (i : Fin m) :
    0 ≤ ∑ j, (SATDeciderTableau.allOnes m n).tableau i j := by
  rw [allOnes_tableau_row_sum]
  exact Nat.cast_nonneg n

end PallLean.Paper93.DeepMath.PathB.Positroid
