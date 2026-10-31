import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarTailExtends

/-!
# Tight switching, step 61: the budget tail in closed form (branch `razborov-recoverRho-wip`)

The per-round survivor budget `hsmall` (steps 36/60) carries an opaque sum — the subcube-relative low-star
weight `∑_{σ extends τ, stars σ < s} pweight p σ`.  The conditional Markov bound `stars_tail_le_extends`
(foundation 24) replaces it by the closed-form Chernoff expression
`((1-p)/2)^(n-stars τ) · (t·p + (1-p))^(stars τ) / t^(s-1)` for any `0 < t ≤ 1`.  So `hsmall` follows from a
*closed-form* inequality in `p, t, s, stars τ, n` and the deep-gate remainder `rest` — no sum left.

* `hsmall_of_chernoff` — the closed-form sufficient condition for the survivor budget.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **Closed-form sufficient condition for the survivor budget.**  Using the conditional Markov tail
(`stars_tail_le_extends`), the opaque low-star sum is bounded by the Chernoff expression
`box · (t·p + (1-p))^(stars τ) / t^(s-1)`; so if that plus the deep-gate remainder `rest` is below the box
mass, the budget `hsmall` holds. -/
theorem hsmall_of_chernoff {p t : ℚ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {s : ℕ} (hs : 1 ≤ s) (τ : Fin n → Option Bool) (rest : ℚ)
    (h : ((1 - p) / 2) ^ (n - stars τ) * (t * p + (1 - p)) ^ (stars τ) / t ^ (s - 1) + rest
          < ((1 - p) / 2) ^ (n - stars τ)) :
    (∑ σ ∈ (extBox τ).filter (fun σ => stars σ < s), pweight p σ) + rest
      < ((1 - p) / 2) ^ (n - stars τ) := by
  have hfilter : (extBox τ).filter (fun σ => stars σ < s)
      = (extBox τ).filter (fun σ => stars σ ≤ s - 1) := Finset.filter_congr (fun σ _ => by omega)
  have hk := stars_tail_le_extends (le_of_lt ht0) ht1 hp0 hp1 τ (s - 1)
  have hpow : (0 : ℚ) < t ^ (s - 1) := pow_pos ht0 _
  have htail : (∑ σ ∈ (extBox τ).filter (fun σ => stars σ < s), pweight p σ)
      ≤ ((1 - p) / 2) ^ (n - stars τ) * (t * p + (1 - p)) ^ (stars τ) / t ^ (s - 1) := by
    rw [hfilter, le_div_iff₀ hpow, mul_comm]
    exact hk
  linarith [htail]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.hsmall_of_chernoff
