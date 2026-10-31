import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CodeCard

/-!
# Block-DT model, foundation 55: branching holography, step 4m — the p-biased measure (branch only)

The measure layer: the p-biased random-restriction weight, and the structural fact that drives the
probability gain — the satisfying boundary `descentSat` has **at most as many stars** as `σ` (it only
*fixes* variables).  Under the p-biased weight, fixing a variable multiplies its weight by
`((1-p)/2)/p`, so a boundary with fewer stars is exponentially lighter — the source of the `(…)^s`
probability factor.

* `pweight p ρ` — the p-biased weight `∏ v, (if ρ v = none then p else (1-p)/2)`.
* `pweight_pos` — it is positive for `0 < p < 1` (a genuine probability weight, per coordinate `p + 2·(1-p)/2 = 1`).
* `stars_le_of_extends` / `stars_descentSat_le` — the boundary fixes more variables, hence has `≤` stars.

## What remains for the full `Pr[depth ≥ s] ≤ (…)^s`

This brick defines the measure and proves the structural driver.  The *quantitative* bound still needs:
  1. the **weight ratio** `pweight p σ = pweight p (descentSat σ) · (2p/(1-p))^(#freed)` (a `Finset.prod`
     split over the freed coordinates) and `#freed ≥ s` on the bad event;
  2. **summing the injection** (brick 54) against `pweight`: `∑_{Bad} pweight ≤ (2p/(1-p))^s · (4^w+1)^F ·
     ∑ pweight ≤ (2p/(1-p))^s · (4^w+1)^F`.
Both are genuine analytic work (and item 1 must reconcile the always-recursing `descentSat` block count
with the depth-`≥ s` event); they are **not** done here.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- The p-biased random-restriction weight: each free coordinate weighs `p`, each fixed coordinate
`(1-p)/2`. -/
def pweight (p : ℚ) (ρ : Fin n → Option Bool) : ℚ :=
  ∏ v : Fin n, (if ρ v = none then p else (1 - p) / 2)

/-- **The p-biased weight is positive** for `0 < p < 1` (a genuine probability weight: per coordinate the
three outcomes `none / some true / some false` weigh `p + (1-p)/2 + (1-p)/2 = 1`). -/
theorem pweight_pos {p : ℚ} (hp0 : 0 < p) (hp1 : p < 1) (ρ : Fin n → Option Bool) :
    0 < pweight p ρ := by
  apply Finset.prod_pos
  intro v _
  by_cases hv : ρ v = none
  · rw [if_pos hv]; exact hp0
  · rw [if_neg hv]; linarith

/-- The per-coordinate weights sum to `1`: this is a probability distribution over `{none, some t, some f}`. -/
theorem pweight_coord_sum (p : ℚ) : p + (1 - p) / 2 + (1 - p) / 2 = 1 := by ring

/-- **Extension cannot increase the star count.**  If `τ` extends `σ` then `τ` fixes at least the
coordinates `σ` does, so `stars τ ≤ stars σ`. -/
theorem stars_le_of_extends {σ τ : Fin n → Option Bool} (h : Extends σ τ) : stars τ ≤ stars σ := by
  apply Finset.card_le_card
  intro v hv
  rw [mem_freeVars] at hv ⊢
  cases hσ : σ v with
  | none => rfl
  | some b => rw [h v b hσ] at hv; simp at hv

/-- **The satisfying boundary has at most as many stars as `σ`** — it only fixes variables.  This is the
structural driver of the p-biased probability gain. -/
theorem stars_descentSat_le (cs : List (Clause n)) (w F : ℕ) (σ : Fin n → Option Bool)
    (x : Fin n → Bool) : stars (descentSat cs w F σ x) ≤ stars σ :=
  stars_le_of_extends (descentSat_extends cs w F σ x)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.pweight_pos
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.stars_descentSat_le
