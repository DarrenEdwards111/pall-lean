import PallLean.Paper93.DeepMath.PathB.Positroid.TableauTraceCoupling
import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB

/-- Scaling property: the trace coupling of an `(m, n)`-tableau is determined by m, n, and entries. -/
theorem tableauTraceCoupling_zero_zero (n : ℕ) :
    tableauTraceCoupling (SATDeciderTableau.zero 0 n) = 0 := by
  unfold tableauTraceCoupling SATDeciderTableau.zero
  simp

/-- Trace coupling of a 1×n zero tableau is 0. -/
theorem tableauTraceCoupling_zero_1xn (n : ℕ) :
    tableauTraceCoupling (SATDeciderTableau.zero 1 n) = 0 := by
  unfold tableauTraceCoupling SATDeciderTableau.zero
  simp

/-- Trace coupling of a 1×n all-ones tableau is n. -/
theorem tableauTraceCoupling_allOnes_1xn (n : ℕ) :
    tableauTraceCoupling (SATDeciderTableau.allOnes 1 n) = (n : ℝ) := by
  unfold tableauTraceCoupling SATDeciderTableau.allOnes
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- Trace coupling of an m×1 all-ones tableau is m. -/
theorem tableauTraceCoupling_allOnes_mx1 (m : ℕ) :
    tableauTraceCoupling (SATDeciderTableau.allOnes m 1) = (m : ℝ) := by
  unfold tableauTraceCoupling SATDeciderTableau.allOnes
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- For square m×m all-ones tableau, trace coupling is m². -/
theorem tableauTraceCoupling_allOnes_square (m : ℕ) :
    tableauTraceCoupling (SATDeciderTableau.allOnes m m) = (m : ℝ)^2 := by
  rw [tableauTraceCoupling_allOnes]
  ring

end PallLean.Paper93.DeepMath.PathB.Positroid
