import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# `√2 − 1 > 0` and `(√2 − 1)(√2 + 1) = 1`

Two small kernel-only facts about `Real.sqrt 2`:

* `one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2`,
* `sqrt_two_minus_one_pos : 0 < Real.sqrt 2 − 1`,
* `sqrt_two_minus_one_times_sqrt_two_plus_one_eq_one :
    (Real.sqrt 2 − 1) * (Real.sqrt 2 + 1) = 1`.

These are conjugate-pair identities used downstream in Path B numeric
work; they only depend on the kernel axioms `propext`,
`Classical.choice`, `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-- `1 < √2`, since `√1 < √2` and `√1 = 1`. -/
theorem one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by
  have h1 : Real.sqrt 1 < Real.sqrt 2 := by
    apply Real.sqrt_lt_sqrt
    · norm_num
    · norm_num
  rw [Real.sqrt_one] at h1
  exact h1

/-- `√2 − 1 > 0`. -/
theorem sqrt_two_minus_one_pos : (0 : ℝ) < Real.sqrt 2 - 1 := by
  have h := one_lt_sqrt_two
  linarith

/-- The conjugate identity `(√2 − 1)(√2 + 1) = 1`, derived from
`√2 · √2 = 2` via `Real.mul_self_sqrt`. -/
theorem sqrt_two_minus_one_times_sqrt_two_plus_one_eq_one :
    (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1) = 1 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  calc (Real.sqrt 2 - 1) * (Real.sqrt 2 + 1)
      = Real.sqrt 2 * Real.sqrt 2 - 1 := by ring
    _ = 2 - 1 := by rw [h]
    _ = 1 := by norm_num

end PallLean.Paper93.DeepMath.PathB
