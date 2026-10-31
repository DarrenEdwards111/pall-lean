import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SwitchingProb

/-!
# Block-DT model, foundation 60: branching holography, step 4r — normalization + the literal probability bound (branch only)

The p-biased weight is a genuine probability distribution: `∑_ρ pweight p ρ = 1` (the per-coordinate
weights `none / some true / some false` sum to `p + (1-p)/2 + (1-p)/2 = 1`, and the sum of products over
all restrictions factors as the product of coordinate sums).  Substituting into brick 59 closes the
switching bound to its literal probability form.

* `pweight_sum_eq_one` — `∑_ρ pweight p ρ = 1` (the distributive law `prod_univ_sum`).
* `descent_switching_le` — `∑_{σ : depth ≥ s} pweight σ ≤ (2p/(1-p))^s · (4^w+1)^F`: the p-biased
  probability that the canonical tree is deep is at most `(2p/(1-p))^s · (4^w+1)^F`.

This is the closing form of the branching switching lemma over the p-biased random restriction.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The p-biased weight is a probability distribution.**  `∑_ρ pweight p ρ = 1`. -/
theorem pweight_sum_eq_one (p : ℚ) : ∑ ρ : Fin n → Option Bool, pweight p ρ = 1 := by
  classical
  have key := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Option Bool)))
    (fun (_ : Fin n) (b : Option Bool) => if b = none then p else (1 - p) / 2)
  rw [Fintype.piFinset_univ] at key
  simp only [pweight]
  rw [← key]
  apply Finset.prod_eq_one
  intro i _
  rw [Fintype.sum_option, Fintype.sum_bool, if_pos rfl, if_neg (by simp), if_neg (by simp)]
  ring

/-- **The literal p-biased switching probability bound.**  For `0 ≤ p ≤ 1/3`, the total p-biased weight of
restrictions whose canonical tree has depth `≥ s` is at most `(2p/(1-p))^s · (4^w+1)^F` (the label space
cardinality).  Since `∑_ρ pweight = 1`, this is `Pr_ρ[depth ≥ s] ≤ (2p/(1-p))^s · (4^w+1)^F`. -/
theorem descent_switching_le {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (w : ℕ) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (F s : ℕ) {Bad : Finset (Fin n → Option Bool)}
    (hBad : ∀ σ ∈ Bad, s ≤ (canonicalDTree cs w F σ).depth) :
    (∑ σ ∈ Bad, pweight p σ)
      ≤ (2 * p / (1 - p)) ^ s
        * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ) := by
  have h := descent_switching_prob hp0 hp3 cs hcons hnd w hw F s hBad
  rwa [pweight_sum_eq_one, mul_one] at h

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.pweight_sum_eq_one
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.descent_switching_le
