import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3H2Union

/-!
# Tight switching, step 85: the union bound from a gate-count bound and a large threshold (branch `razborov-recoverRho-wip`)

The box-free union bound `card · CAP^s/(1-CAP) < 1/2` of the relative capstone (step 83) holds once:

* the rate is slightly tighter than `hr1` — `2·CAP ≤ 1` (i.e. `CAP ≤ 1/2`, e.g. `p ≤ 1/(8wm+1)`), giving the
  geometric decay `CAP^s/(1-CAP) ≤ 2/2^s`; and
* the gate count is bounded (`card ≤ M`) with the threshold large (`4·M < 2^s`).

Then `card · CAP^s/(1-CAP) ≤ 2M/2^s < 1/2`.  No `exp`: just `CAP ≤ 1/2 ⟹ CAP^s ≤ 2^{-s}` and a rational
geometric estimate.

* `h2_of_count_pow` — the union bound from `CAP ≤ 1/2`, `card ≤ M`, `4M < 2^s`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

/-- **The union bound from a gate-count bound and a large threshold.**  With `CAP ≤ 1/2`, `card ≤ M`, and
`4M < 2^s`, the box-free union term is below `1/2`. -/
theorem h2_of_count_pow {CAP card M : ℚ} {s : ℕ} (hcard0 : 0 ≤ card) (hcard : card ≤ M)
    (hcap0 : 0 ≤ CAP) (hcap : 2 * CAP ≤ 1) (hM : 4 * M < 2 ^ s) :
    card * (CAP ^ s / (1 - CAP)) < 1 / 2 := by
  have h1c : (0 : ℚ) < 1 - CAP := by linarith
  have h2s : (0 : ℚ) < 2 ^ s := by positivity
  have hcaps0 : (0 : ℚ) ≤ CAP ^ s := pow_nonneg hcap0 s
  have hcaps : CAP ^ s ≤ (1 / 2) ^ s := pow_le_pow_left₀ hcap0 (by linarith) s
  have hhalf : (1 / 2 : ℚ) ^ s = 1 / 2 ^ s := by rw [div_pow, one_pow]
  rw [hhalf] at hcaps
  -- CAP^s/(1-CAP) ≤ 2/2^s
  have hcd : CAP ^ s / (1 - CAP) ≤ 2 / 2 ^ s := by
    have hcd1 : CAP ^ s / (1 - CAP) ≤ 2 * CAP ^ s := by
      rw [div_le_iff₀ h1c]
      nlinarith [hcaps0, hcap, mul_nonneg hcaps0 (by linarith : (0 : ℚ) ≤ 1 - 2 * CAP)]
    have hci : CAP ^ s ≤ (2 ^ s)⁻¹ := by rwa [one_div] at hcaps
    have hcd2 : 2 * CAP ^ s ≤ 2 / 2 ^ s := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left hci (by norm_num)
    exact le_trans hcd1 hcd2
  -- card * (CAP^s/(1-CAP)) ≤ M * (2/2^s) = 2M/2^s
  have hMnn : (0 : ℚ) ≤ M := le_trans hcard0 hcard
  have hcdnn : (0 : ℚ) ≤ CAP ^ s / (1 - CAP) := div_nonneg hcaps0 (le_of_lt h1c)
  have step : card * (CAP ^ s / (1 - CAP)) ≤ M * (2 / 2 ^ s) :=
    mul_le_mul hcard hcd hcdnn hMnn
  calc card * (CAP ^ s / (1 - CAP)) ≤ M * (2 / 2 ^ s) := step
    _ = 2 * M / 2 ^ s := by ring
    _ < 1 / 2 := by rw [div_lt_iff₀ h2s]; linarith [hM]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.h2_of_count_pow
