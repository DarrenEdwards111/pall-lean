import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarTail
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityRefute

/-!
# Block-DT model, foundation 65: branching holography, step 4w — discharging the concentration hypothesis (branch only)

The concentration arithmetic (item 1): assemble the partition of the star count and the tail bounds so that
the concentration hypothesis `hbig` of brick 62 reduces to a single explicit numeric gap.

* `high_star_weight_eq` — `∑_{s ≤ stars < F} pweight = 1 - ∑_{stars < s} pweight - ∑_{F ≤ stars} pweight`
  (the three star-count ranges partition the probability mass; needs `s ≤ F`).
* `parity_refuted_of_tails` — if the low/high tails are bounded by `Blo`/`Bhi` and
  `cap + Blo + Bhi < 1`, then a width-`≤ w` DNF fails parity on some high-star subcube.  Instantiating
  `Blo`/`Bhi` with the Markov tail bounds (brick 64) discharges brick 62's `hbig` at a concrete gap.

## What this does and does NOT close

This closes the *concentration* step: the parity refutation now follows from a clean numeric gap condition
on the tails (no longer an opaque `hbig`).  It does **not** close `parity ∉ AC⁰`, which additionally needs:
  * the **multi-round AC⁰ circuit reduction** — applying restrictions across all `d` circuit layers so the
    whole circuit collapses to a shallow decision tree (a large separate development, NOT built here);
  * the tighter **`poly(w)`** label base (vs the current `4^w`), which constrains the achievable
    parameter regime where the gap `cap + Blo + Bhi < 1` actually holds (also NOT built).
These are the remaining content of the Håstad lower bound.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The three star ranges partition the mass.**  For `s ≤ F`, the middle range's weight is the total
minus the two tails. -/
theorem high_star_weight_eq (p : ℚ) (s F : ℕ) (hsF : s ≤ F) :
    (∑ ρ ∈ Finset.univ.filter (fun ρ : Fin n → Option Bool => s ≤ stars ρ ∧ stars ρ < F), pweight p ρ)
      = 1 - (∑ ρ ∈ Finset.univ.filter (fun ρ : Fin n → Option Bool => stars ρ < s), pweight p ρ)
          - (∑ ρ ∈ Finset.univ.filter (fun ρ : Fin n → Option Bool => F ≤ stars ρ), pweight p ρ) := by
  classical
  have hge : (∑ ρ ∈ Finset.univ.filter (fun ρ : Fin n → Option Bool => ¬ stars ρ < s), pweight p ρ)
      = 1 - (∑ ρ ∈ Finset.univ.filter (fun ρ : Fin n → Option Bool => stars ρ < s), pweight p ρ) := by
    have := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun ρ : Fin n → Option Bool => stars ρ < s) (pweight p)
    rw [pweight_sum_eq_one] at this
    linarith
  have hset1 : (Finset.univ.filter (fun ρ : Fin n → Option Bool => ¬ stars ρ < s)).filter
      (fun ρ => stars ρ < F) = Finset.univ.filter (fun ρ => s ≤ stars ρ ∧ stars ρ < F) := by
    rw [Finset.filter_filter]; apply Finset.filter_congr; intro ρ _; simp only [not_lt]
  have hset2 : (Finset.univ.filter (fun ρ : Fin n → Option Bool => ¬ stars ρ < s)).filter
      (fun ρ => ¬ stars ρ < F) = Finset.univ.filter (fun ρ => F ≤ stars ρ) := by
    rw [Finset.filter_filter]; apply Finset.filter_congr; intro ρ _; simp only [not_lt]; omega
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter (fun ρ : Fin n → Option Bool => ¬ stars ρ < s))
    (fun ρ => stars ρ < F) (pweight p)
  rw [hset1, hset2, hge] at hsplit
  linarith

/-- **Switching refutes parity, via the tail bounds.**  If the star-count tails are bounded by `Blo`/`Bhi`
and `cap + Blo + Bhi < 1`, then a width-`≤ w` DNF cannot compute parity on all high-star subcubes. -/
theorem parity_refuted_of_tails {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    (cs : List (Clause n)) (hcons : ∀ T ∈ cs, Consistent T)
    (hnd : ∀ T ∈ cs, (T.lits.map litVarOf).Nodup) (w : ℕ) (hw : ∀ T ∈ cs, T.lits.length ≤ w)
    (F s : ℕ) (hsF : s ≤ F) {Blo Bhi : ℚ}
    (hlo : (∑ ρ ∈ Finset.univ.filter (fun ρ : Fin n → Option Bool => stars ρ < s), pweight p ρ) ≤ Blo)
    (hhi : (∑ ρ ∈ Finset.univ.filter (fun ρ : Fin n → Option Bool => F ≤ stars ρ), pweight p ρ) ≤ Bhi)
    (hgap : (2 * p / (1 - p)) ^ s
          * (Fintype.card (Fin F → Option (Fin w → Option (Option Bool))) : ℚ) + Blo + Bhi < 1) :
    ∃ σ : Fin n → Option Bool, s ≤ stars σ ∧ stars σ < F
      ∧ ∃ x, DTree.agreeRestriction σ x ∧ DTree.dnfValue cs x ≠ DTree.parity x := by
  apply parity_refuted_by_switching hp0 hp3 cs hcons hnd w hw F s
  rw [high_star_weight_eq p s F hsF]
  linarith

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.high_star_weight_eq
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_refuted_of_tails
