import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightSwitchingUncond
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TightSwitchingBudget

/-!
# Tight switching, step 32: the unconditional `F`-independent switching budget (branch `razborov-recoverRho-wip`)

`tight_switching_budget` (step 10) with the empty-skip hypotheses dropped: substituting the unconditional
per-shell bound `descent_switching_le_tight_uncond` (step 31) into the depth-shell sum gives

```
  ∑_{ρ : depth ρ ≥ s} pweight p ρ ≤ r^s/(1-r),    r := (2p/(1-p))·(2wm) = 4pwm/(1-p),
```

needing only the width bound `hw` and clause-count bound `hm` — **no `hnf`/`hleaf`/`hpos`**.  `F`-independent
once `r < 1`, i.e. `p ≈ 1/(4wm)`.

* `tight_switching_budget_uncond` — the unconditional `F`-independent switching budget.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The unconditional `F`-independent switching budget.**  No alive/leaf/position hypotheses: the deep-set
p-biased weight is below `r^s/(1-r)` with `r = (2p/(1-p))·(2wm)`. -/
theorem tight_switching_budget_uncond {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s m : ℕ} [NeZero w] [NeZero m] {cs : List (Clause n)}
    (hw : ∀ T ∈ cs, T.lits.length ≤ w) (hm : cs.length ≤ m)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) < 1) :
    (∑ ρ ∈ Finset.univ.filter
        (fun ρ : Restriction n => s ≤ (canonicalDT cs F ρ).depth), pweight p ρ)
      ≤ ((2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) ^ s
          / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ))) := by
  classical
  set r : ℚ := (2 * p / (1 - p)) * (2 * (w : ℚ) * (m : ℚ)) with hr
  have h1p : (0 : ℚ) < 1 - p := by linarith
  have hratio0 : 0 ≤ 2 * p / (1 - p) := div_nonneg (by linarith) (le_of_lt h1p)
  have hr0 : 0 ≤ r := by rw [hr]; exact mul_nonneg hratio0 (by positivity)
  rw [sum_filter_ge_eq_sum_shells (fun ρ : Restriction n => (canonicalDT cs F ρ).depth)
        (pweight p) s F (fun ρ => canonicalDT_depth_le cs F ρ)]
  refine le_trans (Finset.sum_le_sum (fun K _ => ?_))
    (geom_shell_tail_le hr0 hr1 s F)
  have hshell := descent_switching_le_tight_uncond (p := p) hp0 hp3
    (w := w) (F := F) (s := K) (m := m) (cs := cs)
    (Bad := Finset.univ.filter (fun ρ : Restriction n => (canonicalDT cs F ρ).depth = K))
    hw hm (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
  have hcast : (((2 * w * m) ^ K : ℕ) : ℚ) = (2 * (w : ℚ) * (m : ℚ)) ^ K := by push_cast; ring
  rw [hcast, ← mul_pow] at hshell
  exact hshell

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.tight_switching_budget_uncond
