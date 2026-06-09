import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3GeomScheduleBase

/-!
# Tight switching, step 84: the Chernoff gap from the geometric schedule (branch `razborov-recoverRho-wip`)

The Chernoff gap `7·s_{i+1} < s_i·p` of the relative capstone (step 83) holds for the base-`D` geometric
schedule (step 73) once the contraction base beats `7/p` — `(D:ℚ)·p > 7` — and the threshold has not yet
floored (`D ≤ geomSchedB D N i`, i.e. `N ≥ D^{i+1}`).  The key identity is `N/D^{i+1} = (N/D^i)/D`
(`Nat.div_div_eq_div_mul`), so `s_{i+1} = ⌊s_i/D⌋` and `7·⌊s_i/D⌋ ≤ 7·s_i/D < s_i·p` exactly when `D·p > 7`.

* `geomSchedB_gap` — the per-round Chernoff gap for the geometric schedule.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

variable {n : ℕ}

/-- **The Chernoff gap from the geometric schedule.**  With `(D:ℚ)·p > 7` and the round-`i` threshold not yet
floored (`D ≤ geomSchedB D N i`), the gap `7·s_{i+1} < s_i·p` holds. -/
theorem geomSchedB_gap {p : ℚ} {D N i : ℕ} (hp1 : p ≤ 1) (hDp : 7 < (D : ℚ) * p)
    (hN : D ≤ geomSchedB D N i) :
    7 * (geomSchedB D N (i + 1) : ℚ) < (geomSchedB D N i : ℚ) * p := by
  have hp0 : 0 < p := by nlinarith [hDp]
  have hD8 : 8 ≤ D := by
    by_contra h
    push_neg at h
    have hDle : (D : ℚ) ≤ 7 := by exact_mod_cast (by omega : D ≤ 7)
    nlinarith [hDle, hp1, hp0, hDp]
  have hDpos : 0 < D := by omega
  -- the round-i threshold equals N/D^i (no flooring), and is ≥ D
  have hq : D ≤ N / D ^ i := by rw [geomSchedB] at hN; omega
  have hai : geomSchedB D N i = N / D ^ i := by rw [geomSchedB]; omega
  -- the round-(i+1) threshold equals (N/D^i)/D
  have hdiv : N / D ^ (i + 1) = N / D ^ i / D := by rw [pow_succ, Nat.div_div_eq_div_mul]
  have hb1 : 1 ≤ N / D ^ i / D := by rw [Nat.one_le_div_iff hDpos]; exact hq
  have hbi : geomSchedB D N (i + 1) = N / D ^ i / D := by rw [geomSchedB, hdiv]; omega
  rw [hai, hbi]
  -- now: 7 * (N/D^i/D : ℚ) < (N/D^i : ℚ) * p
  set a : ℕ := N / D ^ i with ha
  have hbd : ((a / D : ℕ) : ℚ) * (D : ℚ) ≤ (a : ℚ) := by exact_mod_cast Nat.div_mul_le_self a D
  have hDQ : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hDpos
  have haQ : (0 : ℚ) < (a : ℚ) := by
    have : 0 < a := by omega
    exact_mod_cast this
  nlinarith [hbd, hDp, hDQ, haQ, mul_lt_mul_of_pos_left hDp haQ,
    mul_le_mul_of_nonneg_left hbd (by norm_num : (0 : ℚ) ≤ 7)]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.geomSchedB_gap
