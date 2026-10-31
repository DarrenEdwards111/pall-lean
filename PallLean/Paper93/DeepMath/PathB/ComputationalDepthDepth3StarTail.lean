import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarPGF

/-!
# Block-DT model, foundation 64: branching holography, step 4v — the star-count tail bounds (branch only)

The Markov tail estimates from the star-count generating function (brick 63).  Applying Markov's
inequality to `t^stars`:

* upper tail (`t ≥ 1`): `t^k · ∑_{stars ≥ k} pweight ≤ (t·p + (1-p))^n`.
* lower tail (`0 ≤ t ≤ 1`): `t^k · ∑_{stars ≤ k} pweight ≤ (t·p + (1-p))^n`.

These are exactly the estimates that bound `Pr[stars ≥ F]` and `Pr[stars < s]`, hence lower-bound the
high-star weight `∑_{s ≤ stars < F} pweight` and discharge the concentration hypothesis `hbig` of brick 62
(choosing `t > 1` for the upper tail, `t < 1` for the lower, with `pn` between `s` and `F`).

* `stars_tail_ge` / `stars_tail_le` — the upper/lower Markov tail bounds.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Upper-tail Markov bound.**  For `t ≥ 1`, `t^k · Pr[stars ≥ k] ≤ (t·p + (1-p))^n`. -/
theorem stars_tail_ge {p t : ℚ} (ht : 1 ≤ t) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    t ^ k * (∑ ρ ∈ Finset.univ.filter (fun ρ : Fin n → Option Bool => k ≤ stars ρ), pweight p ρ)
      ≤ (t * p + (1 - p)) ^ n := by
  have ht0 : (0 : ℚ) ≤ t := le_trans zero_le_one ht
  rw [Finset.mul_sum]
  calc ∑ ρ ∈ Finset.univ.filter (fun ρ : Fin n → Option Bool => k ≤ stars ρ), t ^ k * pweight p ρ
      ≤ ∑ ρ ∈ Finset.univ.filter (fun ρ : Fin n → Option Bool => k ≤ stars ρ),
          t ^ (stars ρ) * pweight p ρ := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [Finset.mem_filter] at hρ
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht hρ.2) (pweight_nonneg hp0 hp1 ρ)
    _ ≤ ∑ ρ : Fin n → Option Bool, t ^ (stars ρ) * pweight p ρ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun ρ _ _ => mul_nonneg (pow_nonneg ht0 _) (pweight_nonneg hp0 hp1 ρ))
    _ = (t * p + (1 - p)) ^ n := stars_pgf p t

/-- **Lower-tail Markov bound.**  For `0 ≤ t ≤ 1`, `t^k · Pr[stars ≤ k] ≤ (t·p + (1-p))^n`. -/
theorem stars_tail_le {p t : ℚ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    t ^ k * (∑ ρ ∈ Finset.univ.filter (fun ρ : Fin n → Option Bool => stars ρ ≤ k), pweight p ρ)
      ≤ (t * p + (1 - p)) ^ n := by
  rw [Finset.mul_sum]
  calc ∑ ρ ∈ Finset.univ.filter (fun ρ : Fin n → Option Bool => stars ρ ≤ k), t ^ k * pweight p ρ
      ≤ ∑ ρ ∈ Finset.univ.filter (fun ρ : Fin n → Option Bool => stars ρ ≤ k),
          t ^ (stars ρ) * pweight p ρ := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [Finset.mem_filter] at hρ
        exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ht0 ht1 hρ.2) (pweight_nonneg hp0 hp1 ρ)
    _ ≤ ∑ ρ : Fin n → Option Bool, t ^ (stars ρ) * pweight p ρ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun ρ _ _ => mul_nonneg (pow_nonneg ht0 _) (pweight_nonneg hp0 hp1 ρ))
    _ = (t * p + (1 - p)) ^ n := stars_pgf p t

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.stars_tail_ge
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.stars_tail_le
