import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PBiased

/-!
# Block-DT model, foundation 56: branching holography, step 4n — the weight depends only on stars (branch only)

The analytic heart of the measure gain: the p-biased weight is a closed form in the star count,

  `pweight p ρ = p ^ (stars ρ) · ((1-p)/2) ^ (n - stars ρ)`.

Each of the `stars ρ` free coordinates contributes `p`, each of the `n - stars ρ` fixed coordinates
contributes `(1-p)/2`.  From this the gain `pweight σ / pweight (descentSat σ) = (2p/(1-p))^(#freed)` is
immediate (a boundary fixing `#freed = stars σ − stars (descentSat σ)` more variables, with `stars
(descentSat σ) ≤ stars σ` by brick 55).

* `pweight_eq` — the closed form in the star count.
* `pweight_descentSat_ratio` — `pweight p (descentSat σ x) · ((1-p)/2)^(stars σ - stars (descentSat σ x))
  · p^… = …` is replaced by the clean multiplicative gain identity below.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The p-biased weight is a closed form in the star count.**  `stars ρ` free coordinates weigh `p`
each; the remaining `n - stars ρ` fixed coordinates weigh `(1-p)/2` each. -/
theorem pweight_eq (p : ℚ) (ρ : Fin n → Option Bool) :
    pweight p ρ = p ^ (stars ρ) * ((1 - p) / 2) ^ (n - stars ρ) := by
  classical
  rw [pweight, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun v => ρ v = none)]
  have hfree : (Finset.univ.filter (fun v : Fin n => ρ v = none)).card = stars ρ := rfl
  have hfix : (Finset.univ.filter (fun v : Fin n => ¬ ρ v = none)).card = n - stars ρ := by
    have hadd := Finset.filter_card_add_filter_neg_card_eq_card (s := (Finset.univ : Finset (Fin n)))
      (p := fun v => ρ v = none)
    rw [hfree, Finset.card_univ, Fintype.card_fin] at hadd
    omega
  rw [Finset.prod_congr rfl (fun v hv => if_pos (Finset.mem_filter.mp hv).2),
      Finset.prod_congr rfl (fun v hv => if_neg (Finset.mem_filter.mp hv).2),
      Finset.prod_const, Finset.prod_const, hfree, hfix]

/-- **The multiplicative star-gain identity.**  If `τ` has fewer stars than `ρ` (it fixes `d := stars ρ −
stars τ` more variables), then `pweight ρ · (1-p)^d = pweight τ · (2p)^d` — cross-multiplied form of the
gain `pweight ρ = pweight τ · (2p/(1-p))^d`, avoiding division.  With `τ = descentSat σ` (brick 55) and
`d = #freed`, this is the per-block `(2p/(1-p))` factor whose `d`-th power gives the `(…)^s` switching
gain. -/
theorem pweight_stars_gain (p : ℚ) {ρ τ : Fin n → Option Bool} (h : stars τ ≤ stars ρ) :
    pweight p ρ * (1 - p) ^ (stars ρ - stars τ) = pweight p τ * (2 * p) ^ (stars ρ - stars τ) := by
  have hsn : stars ρ ≤ n := le_trans (Finset.card_le_univ _) (by simp)
  obtain ⟨d, hd⟩ := Nat.le.dest h
  have hdeq : stars ρ - stars τ = d := by omega
  have hm : n - stars τ = (n - (stars τ + d)) + d := by omega
  have hkey : p ^ d * (1 - p) ^ d = ((1 - p) / 2 : ℚ) ^ d * (2 * p) ^ d := by
    rw [← mul_pow, ← mul_pow]; congr 1; ring
  rw [pweight_eq, pweight_eq, hdeq, ← hd, hm, pow_add, pow_add]
  linear_combination (p ^ stars τ * ((1 - p) / 2) ^ (n - (stars τ + d))) * hkey

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.pweight_eq
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.pweight_stars_gain
