import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PNormalize

/-!
# Block-DT model, foundation 63: branching holography, step 4u — the star count is Binomial(n,p) (branch only)

The concentration foundation: under the p-biased measure the star count is `Binomial(n, p)`, captured by
its probability generating function

  `∑_ρ t^(stars ρ) · pweight p ρ = (t·p + (1-p))^n`.

(At `t = 1` this is the normalization `∑ pweight = 1`; the coefficient of `t^k` is `C(n,k) p^k (1-p)^(n-k)`,
the binomial term.)  From this generating function the tail bounds `Pr[stars < s]`, `Pr[stars ≥ F]` follow
by Markov on `t^stars` — discharging the concentration hypothesis `hbig` of brick 62.

* `stars_pgf` — the probability generating function of the star count.

This is the distributional input behind `parity ∉ AC⁰`; the Markov/Chernoff tail estimates on top of it are
standard and left as the next step.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The star-count generating function.**  `∑_ρ t^(stars ρ) · pweight p ρ = (t·p + (1-p))^n` — the star
count is `Binomial(n, p)` under the p-biased measure. -/
theorem stars_pgf (p t : ℚ) :
    (∑ ρ : Fin n → Option Bool, t ^ (stars ρ) * pweight p ρ) = (t * p + (1 - p)) ^ n := by
  classical
  have hterm : ∀ ρ : Fin n → Option Bool,
      t ^ (stars ρ) * pweight p ρ = ∏ v : Fin n, (if ρ v = none then t * p else (1 - p) / 2) := by
    intro ρ
    rw [pweight, show t ^ (stars ρ) = ∏ v : Fin n, (if ρ v = none then t else 1) from ?_]
    · rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : ρ v = none <;> simp [hv]
    · rw [← Finset.prod_filter, Finset.prod_const]; rfl
  rw [Finset.sum_congr rfl (fun ρ _ => hterm ρ)]
  have key := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Option Bool)))
    (fun (_ : Fin n) (b : Option Bool) => if b = none then t * p else (1 - p) / 2)
  rw [Fintype.piFinset_univ] at key
  rw [← key]
  have hcoord : ∀ _i : Fin n,
      (∑ b : Option Bool, (if b = none then t * p else (1 - p) / 2)) = t * p + (1 - p) := by
    intro _i
    rw [Fintype.sum_option, Fintype.sum_bool, if_pos rfl, if_neg (by simp), if_neg (by simp)]
    ring
  rw [Finset.prod_congr rfl (fun i _ => hcoord i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.stars_pgf
