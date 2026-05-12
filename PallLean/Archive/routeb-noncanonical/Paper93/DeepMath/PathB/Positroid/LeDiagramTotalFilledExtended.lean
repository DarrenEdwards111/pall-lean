import PallLean.Paper93.DeepMath.PathB.Positroid.LeDiagramDef
import PallLean.Paper93.DeepMath.PathB.Positroid.LeDiagramTotalCount
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Total filled count of any Le diagram is non-negative. -/
theorem LeDiagram.totalFilledCount_nonneg {k n : ℕ} (D : LeDiagram k n) :
    0 ≤ D.totalFilledCount := Nat.zero_le _

/-- Total filled count of zero diagram is exactly 0. -/
theorem LeDiagram.zero_diagram_count_eq_zero (k n : ℕ) :
    (LeDiagram.zero k n).totalFilledCount = 0 :=
  LeDiagram.zero_totalFilledCount k n

/-- Total filled count of one diagram is exactly k * n. -/
theorem LeDiagram.one_diagram_count_eq_kn (k n : ℕ) :
    (LeDiagram.one k n).totalFilledCount = k * n :=
  LeDiagram.one_totalFilledCount k n

/-- Total filled count is bounded by k * n. -/
theorem LeDiagram.totalFilledCount_max_kn {k n : ℕ} (D : LeDiagram k n) :
    D.totalFilledCount ≤ k * n :=
  LeDiagram.totalFilledCount_le_kn D

end PallLean.Paper93.DeepMath.PathB.Positroid
