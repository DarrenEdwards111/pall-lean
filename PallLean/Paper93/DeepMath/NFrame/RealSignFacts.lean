import Mathlib.Data.Real.Sign

namespace PallLean.Paper93.DeepMath.NFrame

/-- `Real.sign` outputs `-1`, `0`, or `1`. -/
theorem sign_trichotomy (x : ℝ) :
    Real.sign x = -1 ∨ Real.sign x = 0 ∨ Real.sign x = 1 := by
  rcases lt_trichotomy x 0 with h | h | h
  · left; exact Real.sign_of_neg h
  · right; left; rw [h, Real.sign_zero]
  · right; right; exact Real.sign_of_pos h

/-- `Real.sign x * x = |x|` — standard fact. -/
theorem sign_mul_self (x : ℝ) : Real.sign x * x = |x| := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h, neg_one_mul, abs_of_neg h]
  · simp [h]
  · rw [Real.sign_of_pos h, one_mul, abs_of_pos h]

/-- `Real.sign x` is bounded by 1 in absolute value. -/
theorem sign_le_one (x : ℝ) : Real.sign x ≤ 1 := by
  rcases sign_trichotomy x with h | h | h <;> rw [h] <;> norm_num

theorem neg_one_le_sign (x : ℝ) : -1 ≤ Real.sign x := by
  rcases sign_trichotomy x with h | h | h <;> rw [h] <;> norm_num

end PallLean.Paper93.DeepMath.NFrame
