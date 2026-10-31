import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HcfSplit

/-!
# Tight switching, step 69: a rational Bernoulli tail bound (branch `razborov-recoverRho-wip`)

The Chernoff atom `h1` of the per-round inequality (step 67) needs a decay bound on `(1-x)^k` — but in `ℚ`
(no `exp`/`log`).  The Bernoulli inequality supplies a rational one: `(1-x)^k ≤ 1/(1+k·x)`, via `(1-x) ≤
1/(1+x)` (from `(1-x)(1+x) = 1-x² ≤ 1`) and `(1+x)^k ≥ 1+k·x` (Mathlib's `one_add_mul_le_pow`).  This is the
genuine rational concentration tool the switching-lemma tail estimate is built from.

* `one_sub_pow_le_inv_one_add_mul` — `(1-x)^k ≤ 1/(1+k·x)` for `0 ≤ x ≤ 1`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

/-- **Rational Bernoulli tail bound.**  For `0 ≤ x ≤ 1`, `(1-x)^k ≤ 1/(1+k·x)`. -/
theorem one_sub_pow_le_inv_one_add_mul {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    (1 - x) ^ k ≤ 1 / (1 + (k : ℚ) * x) := by
  have h1x : (0 : ℚ) < 1 + x := by linarith
  have hbase : (0 : ℚ) ≤ 1 - x := by linarith
  have hstep1 : (1 - x) ≤ 1 / (1 + x) := by
    rw [le_div_iff₀ h1x]; nlinarith [sq_nonneg x]
  have hstep2 : (1 - x) ^ k ≤ (1 / (1 + x)) ^ k := pow_le_pow_left₀ hbase hstep1 k
  rw [div_pow, one_pow] at hstep2
  have hbern : 1 + (k : ℚ) * x ≤ (1 + x) ^ k := one_add_mul_le_pow (by linarith) k
  have hpos : (0 : ℚ) < 1 + (k : ℚ) * x := by positivity
  exact le_trans hstep2 (one_div_le_one_div_of_le hpos hbern)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.one_sub_pow_le_inv_one_add_mul
