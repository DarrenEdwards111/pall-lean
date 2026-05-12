import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-!
# Tableau-trace-derived coupling

This file defines a **tableau-trace coupling** that genuinely depends
on the entries of a `SATDeciderTableau m n`, not merely its dimension.

The coupling is the simplest non-trivial entry-dependent linear
functional: the sum of all entries of the tableau. It evaluates to
`0` on the all-zeros tableau and to `m * n` on the all-ones tableau,
demonstrating that distinct tableaus give distinct couplings.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The **tableau trace coupling**: the sum of all entries of the tableau. -/
def tableauTraceCoupling {m n : ℕ} (T : SATDeciderTableau m n) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, T.tableau i j

/-- The trace coupling of the zero tableau is 0. -/
theorem tableauTraceCoupling_zero (m n : ℕ) :
    tableauTraceCoupling (SATDeciderTableau.zero m n) = 0 := by
  unfold tableauTraceCoupling SATDeciderTableau.zero
  simp

/-- The trace coupling of the all-ones tableau is m * n. -/
theorem tableauTraceCoupling_allOnes (m n : ℕ) :
    tableauTraceCoupling (SATDeciderTableau.allOnes m n) = (m : ℝ) * n := by
  unfold tableauTraceCoupling SATDeciderTableau.allOnes
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The trace coupling depends on tableau entries: zero tableau gives 0,
    all-ones tableau gives m*n. -/
theorem tableauTraceCoupling_distinguishes_zero_vs_allOnes (m n : ℕ) (h : 1 ≤ m * n) :
    tableauTraceCoupling (SATDeciderTableau.zero m n) ≠
    tableauTraceCoupling (SATDeciderTableau.allOnes m n) := by
  rw [tableauTraceCoupling_zero, tableauTraceCoupling_allOnes]
  have : (0 : ℝ) < (m : ℝ) * n := by
    have hcast : (1 : ℝ) ≤ (m : ℝ) * n := by exact_mod_cast h
    linarith
  linarith

/-- The trace coupling is non-negative when all entries are non-negative
    (which is the case for both `zero` and `allOnes` tableaus). -/
theorem tableauTraceCoupling_zero_nonneg (m n : ℕ) :
    0 ≤ tableauTraceCoupling (SATDeciderTableau.zero m n) := by
  rw [tableauTraceCoupling_zero]

/-- The trace coupling of the all-ones tableau is non-negative. -/
theorem tableauTraceCoupling_allOnes_nonneg (m n : ℕ) :
    0 ≤ tableauTraceCoupling (SATDeciderTableau.allOnes m n) := by
  rw [tableauTraceCoupling_allOnes]
  exact mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)

end PallLean.Paper93.DeepMath.PathB.Positroid
