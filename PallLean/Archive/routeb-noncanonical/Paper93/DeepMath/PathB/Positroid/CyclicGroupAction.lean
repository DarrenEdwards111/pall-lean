import PallLean.Paper93.DeepMath.PathB.Positroid.CyclicShift
import Mathlib.Logic.Equiv.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The cyclic shift composed with itself k times. -/
def cyclicShiftIter (n : ℕ) (hn : 0 < n) (k : ℕ) : Fin n ≃ Fin n :=
  match k with
  | 0 => Equiv.refl (Fin n)
  | k+1 => (cyclicShiftIter n hn k).trans (cyclicShiftPos n hn)

/-- 0-th iterate is identity. -/
theorem cyclicShiftIter_zero (n : ℕ) (hn : 0 < n) (i : Fin n) :
    cyclicShiftIter n hn 0 i = i := rfl

/-- First iterate equals cyclicShiftPos. -/
theorem cyclicShiftIter_one (n : ℕ) (hn : 0 < n) (i : Fin n) :
    cyclicShiftIter n hn 1 i = cyclicShiftPos n hn i := by
  unfold cyclicShiftIter
  rfl

/-- The 0-th iterate is the identity equivalence. -/
theorem cyclicShiftIter_zero_id (n : ℕ) (hn : 0 < n) :
    cyclicShiftIter n hn 0 = Equiv.refl (Fin n) := rfl

end PallLean.Paper93.DeepMath.PathB.Positroid
