import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FreedCount

/-!
# Block-DT model, foundation 58: branching holography, step 4p — the per-restriction weight gain (branch only)

The per-restriction probability gain, in the form the weighted sum needs.  For `0 ≤ p ≤ 1/3` the ratio
`r := 2p/(1-p)` satisfies `0 ≤ r ≤ 1`, so a restriction with `≥ s` more stars than `τ` is `≤ r^s` times as
heavy: `pweight σ ≤ r^s · pweight τ`.  On the bad event the boundary `descentSat σ` fixes `≥ s` variables
(brick 57), so `pweight σ ≤ r^s · pweight (descentSat σ)`.

* `pweight_nonneg` — `0 ≤ pweight p ρ` for `0 ≤ p ≤ 1`.
* `pweight_le_ratio_pow` — `pweight σ ≤ (2p/(1-p))^s · pweight τ` when `s ≤ stars σ − stars τ`.
* `pweight_bad_le` — on the bad event, `pweight σ ≤ (2p/(1-p))^s · pweight (descentSat σ x)` for the
  deepest input `x`.

Only the `Finset.sum`-over-injection step then remains for the full `Pr[depth ≥ s] ≤ (2p/(1-p))^s·(4^w+1)^F`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The p-biased weight is nonnegative for `0 ≤ p ≤ 1`. -/
theorem pweight_nonneg {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ : Fin n → Option Bool) :
    0 ≤ pweight p ρ := by
  apply Finset.prod_nonneg
  intro v _
  by_cases hv : ρ v = none
  · rw [if_pos hv]; exact hp0
  · rw [if_neg hv]; linarith

/-- **The per-restriction weight gain.**  A restriction with `≥ s` more stars than `τ` is `≤ (2p/(1-p))^s`
times as heavy (for `0 ≤ p ≤ 1/3`). -/
theorem pweight_le_ratio_pow {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {σ τ : Fin n → Option Bool} (hst : stars τ ≤ stars σ) {s : ℕ} (hs : s ≤ stars σ - stars τ) :
    pweight p σ ≤ (2 * p / (1 - p)) ^ s * pweight p τ := by
  have hp1 : (0 : ℚ) < 1 - p := by linarith
  set d := stars σ - stars τ with hd
  set r := 2 * p / (1 - p) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr, div_le_one hp1]; linarith
  have hgain := pweight_stars_gain p hst
  have h1p : ((1 - p) : ℚ) ^ d ≠ 0 := by positivity
  have hpw : pweight p σ = pweight p τ * r ^ d := by
    rw [hr, div_pow, ← mul_div_assoc, eq_div_iff h1p]
    linear_combination hgain
  rw [hpw]
  have hτ : 0 ≤ pweight p τ := pweight_nonneg hp0 (by linarith) τ
  have hrd : r ^ d ≤ r ^ s := pow_le_pow_of_le_one hr0 hr1 hs
  calc pweight p τ * r ^ d ≤ pweight p τ * r ^ s := mul_le_mul_of_nonneg_left hrd hτ
    _ = r ^ s * pweight p τ := by ring

/-- **The per-restriction gain on the bad event.**  If the canonical tree has depth `≥ s`, then for the
deepest input the boundary is `≤ (2p/(1-p))^s` lighter. -/
theorem pweight_bad_le {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1) (cs : List (Clause n)) (w : ℕ)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (F : ℕ) (σ : Fin n → Option Bool) (s : ℕ)
    (hs : s ≤ (canonicalDTree cs w F σ).depth) :
    ∃ x, pweight p σ ≤ (2 * p / (1 - p)) ^ s * pweight p (descentSat cs w F σ x) := by
  obtain ⟨x, hx⟩ := freed_ge_of_depth_ge cs w hnd F σ s hs
  refine ⟨x, ?_⟩
  exact pweight_le_ratio_pow hp0 hp3 (stars_descentSat_le cs w F σ x) (by omega)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.pweight_bad_le
