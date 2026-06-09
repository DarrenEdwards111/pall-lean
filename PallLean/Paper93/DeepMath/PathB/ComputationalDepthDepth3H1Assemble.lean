import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3EulerBound

/-!
# Tight switching, step 71: assembling the Chernoff atom `h1` (branch `razborov-recoverRho-wip`)

The Chernoff atom `h1` of the per-round inequality (step 67) assembled from the two rational atoms, at the
Markov parameter `t = 1 - 1/s_out`:

* the numerator `((1-1/s_out)·p + (1-p))^(stars τ) = (1 - p/s_out)^(stars τ)` decays by the Bernoulli bound
  (step 69): `≤ 1/(1 + (stars τ)·p/s_out)`;
* the denominator `(1-1/s_out)^(s_out-1) ≥ 1/4` by the Euler ceiling (step 70).

So the term is `≤ 4/(1 + (stars τ)·p/s_out)`, which is `< 1/2` exactly when `(stars τ)·p > 7·s_out` — the clean
rational *gap condition* with no `exp`.

* `t_pow_ge_quarter` — `(1-1/s_out)^(s_out-1) ≥ 1/4`.
* `h1_of_gap` — the Chernoff atom from the gap condition.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

/-- **The Markov `t`-factor is bounded below.**  `(1-1/s)^(s-1) ≥ 1/4` for `s ≥ 1`, from the Euler ceiling. -/
theorem t_pow_ge_quarter (sOut : ℕ) (hs : 1 ≤ sOut) :
    (1 : ℚ) / 4 ≤ (1 - 1 / (sOut : ℚ)) ^ (sOut - 1) := by
  rcases Nat.lt_or_ge sOut 2 with h | h
  · interval_cases sOut; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, sOut = m + 1 := ⟨sOut - 1, by omega⟩
    have hm1 : 1 ≤ m := by omega
    have hmne : (m : ℚ) ≠ 0 := by positivity
    have hid : (1 - 1 / ((m : ℚ) + 1)) = 1 / (1 + 1 / (m : ℚ)) := by
      rw [eq_div_iff (by positivity)]; field_simp; ring
    have hkey : (1 - 1 / (((m + 1 : ℕ) : ℚ))) ^ ((m + 1) - 1) = 1 / (1 + 1 / (m : ℚ)) ^ m := by
      push_cast
      rw [hid, div_pow, one_pow]
    rw [hkey]
    have heuler := one_add_inv_pow_le_four m
    have hpos : (0 : ℚ) < (1 + 1 / (m : ℚ)) ^ m := by positivity
    rw [le_div_iff₀ hpos]
    linarith

/-- **The Chernoff atom from the gap condition.**  At `t = 1 - 1/s_out`, if `(stars τ)·p > 7·s_out` then the
per-round Chernoff term is below `1/2`. -/
theorem h1_of_gap {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (starsτ sOut : ℕ) (hs : 1 ≤ sOut)
    (hgap : 7 * (sOut : ℚ) < (starsτ : ℚ) * p) :
    ((1 - 1 / (sOut : ℚ)) * p + (1 - p)) ^ starsτ / (1 - 1 / (sOut : ℚ)) ^ (sOut - 1) < 1 / 2 := by
  have hsQ : (0 : ℚ) < (sOut : ℚ) := by exact_mod_cast hs
  have hsQ1 : (1 : ℚ) ≤ (sOut : ℚ) := by exact_mod_cast hs
  -- base rewrite: t·p + (1-p) = 1 - p/s_out
  have hbase : (1 - 1 / (sOut : ℚ)) * p + (1 - p) = 1 - p / (sOut : ℚ) := by
    field_simp; ring
  rw [hbase]
  -- numerator decay (Bernoulli)
  set x : ℚ := p / (sOut : ℚ) with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hsQ]; linarith [hsQ1]
  have hnum : (1 - x) ^ starsτ ≤ 1 / (1 + (starsτ : ℚ) * x) :=
    one_sub_pow_le_inv_one_add_mul hx0 hx1 starsτ
  have hnum0 : (0 : ℚ) ≤ (1 - x) ^ starsτ := by
    apply pow_nonneg; linarith
  -- denominator ≥ 1/4
  have hden : (1 : ℚ) / 4 ≤ (1 - 1 / (sOut : ℚ)) ^ (sOut - 1) := t_pow_ge_quarter sOut hs
  have hden0 : (0 : ℚ) < (1 - 1 / (sOut : ℚ)) ^ (sOut - 1) := by linarith
  -- the gap gives 1 + starsτ·x > 8
  have hR : (8 : ℚ) < 1 + (starsτ : ℚ) * x := by
    have hxe : (starsτ : ℚ) * x = (starsτ : ℚ) * p / (sOut : ℚ) := by rw [hx]; ring
    rw [hxe]
    have h7 : (7 : ℚ) < (starsτ : ℚ) * p / (sOut : ℚ) := by
      rw [lt_div_iff₀ hsQ]; linarith [hgap]
    linarith
  have hRpos : (0 : ℚ) < 1 + (starsτ : ℚ) * x := by linarith
  -- term ≤ (1-x)^starsτ / (1/4) = 4·(1-x)^starsτ ≤ 4/(1+starsτ·x) < 1/2
  calc (1 - x) ^ starsτ / (1 - 1 / (sOut : ℚ)) ^ (sOut - 1)
      ≤ (1 - x) ^ starsτ / (1 / 4) :=
        div_le_div_of_nonneg_left hnum0 (by norm_num) hden
    _ = 4 * (1 - x) ^ starsτ := by ring
    _ ≤ 4 * (1 / (1 + (starsτ : ℚ) * x)) := by linarith
    _ = 4 / (1 + (starsτ : ℚ) * x) := by ring
    _ < 1 / 2 := by rw [div_lt_iff₀ hRpos]; linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.h1_of_gap
