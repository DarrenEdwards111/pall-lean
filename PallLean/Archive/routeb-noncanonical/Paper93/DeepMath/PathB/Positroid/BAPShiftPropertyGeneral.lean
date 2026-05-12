import PallLean.Paper93.DeepMath.PathB.Positroid.BoundedAffinePerm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The shift property f(i+kn) = f(i) + kn iterates to all multiples of n. -/
theorem BAP_shift_property_iter {n : ℕ} (b : BoundedAffinePerm n) (i : ℤ) (k : ℕ) :
    b.toFun (i + k * n) = b.toFun i + k * n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by
      simp [Nat.cast_succ]
    have hrw : i + ((k + 1 : ℕ) : ℤ) * (n : ℤ) = (i + (k : ℤ) * (n : ℤ)) + (n : ℤ) := by
      rw [hcast]; ring
    rw [hrw]
    rw [b.shift_property]
    rw [ih]
    rw [hcast]
    ring

/-- The shift property applied at i = 0 gives b(kn) = b(0) + kn. -/
theorem BAP_shift_at_zero {n : ℕ} (b : BoundedAffinePerm n) (k : ℕ) :
    b.toFun (k * n) = b.toFun 0 + k * n := by
  have := BAP_shift_property_iter b 0 k
  rw [zero_add] at this
  exact this

end PallLean.Paper93.DeepMath.PathB.Positroid
