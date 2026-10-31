import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarTail
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PWeightExtends

/-!
# AC⁰ reduction, foundation 24: conditional star concentration (branch only)

The survivor lower bound for subcube-relative switching.  Conditioned on extending `τ`, the star count is
`Binomial(stars τ, p)` (only the `τ`-free coordinates can survive), captured by the conditional generating
function

  `∑_{σ extends τ} t^(stars σ) · pweight p σ = ((1-p)/2)^(n - stars τ) · (t·p + (1-p))^(stars τ)`.

The `((1-p)/2)^(n - stars τ)` factor is the conditioning constant (brick 22); the `(t·p + (1-p))^(stars τ)`
factor is the Binomial PGF over the `stars τ` free coordinates.  Markov on `t^stars` then bounds the
conditional lower tail `Pr[stars σ ≤ k | extends τ]` — so a *good* extending restriction (brick 23) keeps
`stars` large, the survivor bound the coordinate budget needs.

* `stars_pgf_extends` — the conditional star generating function.
* `stars_tail_le_extends` — the conditional lower-tail Markov bound.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The conditional star generating function.**  Conditioned on extending `τ`, the star count is
`Binomial(stars τ, p)`: the `τ`-free coordinates contribute the PGF `(t·p + (1-p))^(stars τ)`, the fixed
ones the constant `((1-p)/2)^(n - stars τ)`. -/
theorem stars_pgf_extends (p t : ℚ) (τ : Fin n → Option Bool) :
    (∑ σ ∈ extBox τ, t ^ (stars σ) * pweight p σ)
      = ((1 - p) / 2) ^ (n - stars τ) * (t * p + (1 - p)) ^ (stars τ) := by
  classical
  have hterm : ∀ σ : Fin n → Option Bool,
      t ^ (stars σ) * pweight p σ = ∏ v : Fin n, (if σ v = none then t * p else (1 - p) / 2) := by
    intro σ
    rw [pweight, show t ^ (stars σ) = ∏ v : Fin n, (if σ v = none then t else 1) from ?_]
    · rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : σ v = none <;> simp [hv]
    · rw [← Finset.prod_filter, Finset.prod_const]; rfl
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ), extBox,
    ← Finset.prod_univ_sum (fun v => if τ v = none then (Finset.univ : Finset (Option Bool)) else {τ v})
      (fun (_ : Fin n) (b : Option Bool) => if b = none then t * p else (1 - p) / 2)]
  have hfac : ∀ v ∈ (Finset.univ : Finset (Fin n)),
      (∑ b ∈ (if τ v = none then (Finset.univ : Finset (Option Bool)) else {τ v}),
        (if b = none then t * p else (1 - p) / 2))
        = (if τ v = none then (t * p + (1 - p)) else (1 - p) / 2) := by
    intro v _
    by_cases hv : τ v = none
    · rw [if_pos hv, if_pos hv, Fintype.sum_option, Fintype.sum_bool, if_pos rfl,
        if_neg (by simp), if_neg (by simp)]
      ring
    · rw [if_neg hv, if_neg hv, Finset.sum_singleton, if_neg hv]
  rw [Finset.prod_congr rfl hfac, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hcard1 : (Finset.univ.filter (fun v : Fin n => τ v = none)).card = stars τ := by
    rw [stars, freeVars]
  have hcard2 : (Finset.univ.filter (fun v : Fin n => ¬ τ v = none)).card = n - stars τ := by
    have h : (Finset.univ.filter (fun v : Fin n => τ v = none)).card
        + (Finset.univ.filter (fun v : Fin n => ¬ τ v = none)).card = n := by
      rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ, Fintype.card_fin]
    omega
  rw [hcard1, hcard2, mul_comm]

/-- **The conditional lower-tail Markov bound.**  For `0 ≤ t ≤ 1`, the conditional weight of restrictions
extending `τ` with at most `k` stars is exponentially small in `k` relative to the conditioning constant. -/
theorem stars_tail_le_extends {p t : ℚ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (τ : Fin n → Option Bool) (k : ℕ) :
    t ^ k * (∑ σ ∈ (extBox τ).filter (fun σ => stars σ ≤ k), pweight p σ)
      ≤ ((1 - p) / 2) ^ (n - stars τ) * (t * p + (1 - p)) ^ (stars τ) := by
  rw [Finset.mul_sum]
  calc ∑ σ ∈ (extBox τ).filter (fun σ => stars σ ≤ k), t ^ k * pweight p σ
      ≤ ∑ σ ∈ (extBox τ).filter (fun σ => stars σ ≤ k), t ^ (stars σ) * pweight p σ := by
        apply Finset.sum_le_sum
        intro σ hσ
        rw [Finset.mem_filter] at hσ
        exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ht0 ht1 hσ.2)
          (pweight_nonneg hp0 hp1 σ)
    _ ≤ ∑ σ ∈ extBox τ, t ^ (stars σ) * pweight p σ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun σ _ _ => mul_nonneg (pow_nonneg ht0 _) (pweight_nonneg hp0 hp1 σ))
    _ = ((1 - p) / 2) ^ (n - stars τ) * (t * p + (1 - p)) ^ (stars τ) := stars_pgf_extends p t τ

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.stars_pgf_extends
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.stars_tail_le_extends
