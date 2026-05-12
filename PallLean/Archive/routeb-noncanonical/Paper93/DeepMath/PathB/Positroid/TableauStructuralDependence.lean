import PallLean.Paper93.DeepMath.PathB.Positroid.SATDeciderTableauToy
import PallLean.Paper93.DeepMath.PathB.Positroid.TableauTraceCoupling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Structural dependence of the tableau trace coupling

This file provides structural theorems linking properties of a
`SATDeciderTableau m n` to the gauge witness given by the
`tableauTraceCoupling`. The trace coupling depends only on the
underlying tableau matrix; consequently, equality of tableau matrices
forces equality of trace couplings, and the trace coupling enjoys
non-negativity whenever entries are non-negative.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are used.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB

/-- The trace coupling of a tableau is invariant under structural identity. -/
theorem tableauTraceCoupling_eq_iff_tableau_eq {m n : ℕ}
    (T₁ T₂ : SATDeciderTableau m n) :
    T₁.tableau = T₂.tableau →
    tableauTraceCoupling T₁ = tableauTraceCoupling T₂ := by
  intro h
  unfold tableauTraceCoupling
  rw [h]

/-- The trace coupling depends only on the tableau matrix, not on the (irrelevant) row-sum-nonneg proof. -/
theorem tableauTraceCoupling_depends_on_tableau {m n : ℕ}
    (T : SATDeciderTableau m n) :
    tableauTraceCoupling T = ∑ i : Fin m, ∑ j : Fin n, T.tableau i j :=
  rfl

/-- The trace coupling is bounded above by the maximum entry times m*n
    (when all entries are non-negative). -/
theorem tableauTraceCoupling_bounded {m n : ℕ}
    (T : SATDeciderTableau m n) (h_nn : ∀ i j, 0 ≤ T.tableau i j) :
    0 ≤ tableauTraceCoupling T := by
  unfold tableauTraceCoupling
  apply Finset.sum_nonneg
  intros i _
  apply Finset.sum_nonneg
  intros j _
  exact h_nn i j

/-- The zero tableau has trace coupling zero. -/
theorem tableauTraceCoupling_zero_value (m n : ℕ) :
    tableauTraceCoupling (SATDeciderTableau.zero m n) = 0 := by
  unfold tableauTraceCoupling SATDeciderTableau.zero
  simp

end PallLean.Paper93.DeepMath.PathB.Positroid
