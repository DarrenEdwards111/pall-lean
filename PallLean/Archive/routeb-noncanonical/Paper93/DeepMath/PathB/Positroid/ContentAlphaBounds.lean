import PallLean.Paper93.DeepMath.PathB.Positroid.ContentDrivenAlpha
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic.Linarith

namespace PallLean.Paper93.DeepMath.PathB.Positroid
open PallLean.Paper93.DeepMath.PathB

theorem contentDrivenAlpha_le_one_plus_abs {m n : ℕ} (T : SATDeciderTableau m n) :
    contentDrivenAlpha T ≤ 1 + |tableauTraceCoupling T| := by
  unfold contentDrivenAlpha
  exact le_refl _

theorem contentDrivenAlpha_ge_one_zero_tableau (m n : ℕ) :
    contentDrivenAlpha (SATDeciderTableau.zero m n) = 1 :=
  contentDrivenAlpha_zero m n

theorem contentDrivenAlpha_increases_with_allOnes (m n : ℕ) (h : 1 ≤ m * n) :
    contentDrivenAlpha (SATDeciderTableau.zero m n) <
    contentDrivenAlpha (SATDeciderTableau.allOnes m n) := by
  rw [contentDrivenAlpha_zero, contentDrivenAlpha_allOnes]
  have hmn : (1 : ℝ) ≤ (m : ℝ) * n := by exact_mod_cast h
  linarith

theorem contentDrivenAlpha_at_zero_eq_one :
    contentDrivenAlpha (SATDeciderTableau.zero 2 2) = 1 :=
  contentDrivenAlpha_zero 2 2

theorem contentDrivenAlpha_at_allOnes_22_eq_5 :
    contentDrivenAlpha (SATDeciderTableau.allOnes 2 2) = 5 := by
  rw [contentDrivenAlpha_allOnes]; norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid
