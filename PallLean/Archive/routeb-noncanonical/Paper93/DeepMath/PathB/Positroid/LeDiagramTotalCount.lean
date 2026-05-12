import PallLean.Paper93.DeepMath.PathB.Positroid.LeDiagramDef
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Total filled-cell counts in Le diagrams

This file proves structural properties about counting filled cells in Le
diagrams.  We define `LeDiagram.totalFilledCount` as the sum over all cells
of the indicator that the cell is filled, and establish:

* the zero diagram has total count `0`;
* the all-ones diagram has total count `k * n`;
* every Le diagram has total count at most `k * n`.

The file is kernel-only: no `sorry`, no custom `axiom`, only the kernel
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The total count of filled cells in a Le diagram. -/
def LeDiagram.totalFilledCount {k n : ℕ} (D : LeDiagram k n) : ℕ :=
  ∑ i : Fin k, ∑ j : Fin n, (if D.filling i j = true then 1 else 0)

/-- The total count of filled cells in the zero diagram is 0. -/
theorem LeDiagram.zero_totalFilledCount (k n : ℕ) :
    (LeDiagram.zero k n).totalFilledCount = 0 := by
  unfold LeDiagram.totalFilledCount
  simp [LeDiagram.zero]

/-- The total count of filled cells in the all-ones diagram is k*n. -/
theorem LeDiagram.one_totalFilledCount (k n : ℕ) :
    (LeDiagram.one k n).totalFilledCount = k * n := by
  unfold LeDiagram.totalFilledCount
  simp only [LeDiagram.one, if_true]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- The total filled count is at most k*n for any Le diagram. -/
theorem LeDiagram.totalFilledCount_le_kn {k n : ℕ} (D : LeDiagram k n) :
    D.totalFilledCount ≤ k * n := by
  unfold LeDiagram.totalFilledCount
  calc ∑ i : Fin k, ∑ j : Fin n, (if D.filling i j = true then 1 else 0)
      ≤ ∑ i : Fin k, ∑ j : Fin n, 1 := by
        apply Finset.sum_le_sum
        intros i _
        apply Finset.sum_le_sum
        intros j _
        split <;> norm_num
    _ = k * n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

end PallLean.Paper93.DeepMath.PathB.Positroid
