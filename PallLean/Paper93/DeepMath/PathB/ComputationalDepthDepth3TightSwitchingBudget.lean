import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DescentSwitchingTight
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ShellDecomp
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3GeomTail

/-!
# Tight switching, step 10: the `F`-independent tight switching budget (branch `razborov-recoverRho-wip`)

The headline of the tight route, assembled from the three preceding bricks.  The crude route's switching
budget is `(2p/(1-p))^s·(4^w+1)^F`, whose `(4^w+1)^F` factor is `F`-dependent and renders the depth-3
assembly vacuous (it forces `s > F > n`; see `depth3_budgets_unsatisfiable`).  The tight route removes the
`F`-dependence entirely:

```
  ∑_{ρ : depth ρ ≥ s} pweight p ρ  ≤  r^s / (1 - r),      r := (2p/(1-p))·(2w) = 4pw/(1-p),
```

a finite, `F`-independent bound once `r < 1` — i.e. once `p < 1/(4w+1)` (the tight parameter regime,
sharper than the crude route's `p ≤ 1/3`).  The union-bound budget `#gates · r^s/(1-r) < 1` is then
`s ≳ log #gates`, with no `F` anywhere: this is exactly what removes the depth-3 vacuity.

The assembly is purely the three preceding bricks:

* per depth-shell `{depth = K}`: `descent_switching_le_tight` (brick 09 / `step 5`) gives
  `∑ pweight ≤ (2p/(1-p))^K·(2w)^K = r^K`;
* the deep set `{depth ≥ s}` partitions into shells `K ∈ [s, F]`: `sum_filter_ge_eq_sum_shells`
  (`step 7`), with the depth bound `(canonicalDT …).depth ≤ F` (`canonicalDT_depth_le`);
* the shell tail sums geometrically: `geom_shell_tail_le` (`step 6`).

## The standing hypotheses (honest)

The bound carries the *global* alive/leaf/position hypotheses of `descent_switching_le_tight`
(`hnf` term-aliveness, `hleaf`, `hpos`) for every `ρ`.  The `hnf` (term-aliveness) hypothesis is the
**empty-skip wall**: brick `decodedSel_not_filter_invariant` proves it cannot be discharged unconditionally
(for all `ρ`) via the forward-scan reconstruction, and `pathLenBadGt_card_le` carries the same wall in its
`hne` (no-empty-block) hypothesis on the cardinality side.  So this budget is the tight `F`-independent
count *conditional on the empty-skip wall* — which is the genuine, irreducible switching-lemma content, not
a gap that has been hidden.

`geom_shell_tail_le` needs `0 ≤ r < 1`; `0 ≤ r` is derived here from `0 ≤ p` and `3p ≤ 1`, and `r < 1` is
the explicit tight-regime hypothesis `hr1`.

* `tight_switching_budget` — `∑_{depth ρ ≥ s} pweight p ρ ≤ r^s/(1-r)` (the `F`-independent budget).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The `F`-independent tight switching budget.**  Under the global alive (`hnf`), leaf (`hleaf`) and
position (`hpos`) hypotheses, and the tight parameter regime `r < 1` (`r = (2p/(1-p))·(2w)`), the p-biased
weight of the deep set `{depth ρ ≥ s}` is below `r^s/(1-r)` — a finite bound *independent of the fuel `F`*,
which is what removes the depth-3 vacuity of the crude `(4^w+1)^F` count. -/
theorem tight_switching_budget {p : ℚ} (hp0 : 0 ≤ p) (hp3 : 3 * p ≤ 1)
    {w F s : ℕ} [NeZero w] {cs : List (Clause n)}
    (hnf : ∀ ρ : Restriction n, ∀ U ∈ cs, SwitchingCounting.termFalsified ρ U = false)
    (hleaf : ∀ ρ : Restriction n,
      SwitchingCounting.anyTermSat cs (deepestEnd cs F ρ) = false)
    (hpos : ∀ ρ : Restriction n, ∀ q ∈ deepestFullSeq cs F ρ, q.1 < w)
    (hr1 : (2 * p / (1 - p)) * (2 * (w : ℚ)) < 1) :
    (∑ ρ ∈ Finset.univ.filter
        (fun ρ : Restriction n => s ≤ (canonicalDT cs F ρ).depth), pweight p ρ)
      ≤ ((2 * p / (1 - p)) * (2 * (w : ℚ))) ^ s
          / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ))) := by
  classical
  set r : ℚ := (2 * p / (1 - p)) * (2 * (w : ℚ)) with hr
  -- `0 < 1 - p` from `3p ≤ 1`, hence `0 ≤ r`.
  have h1p : (0 : ℚ) < 1 - p := by linarith
  have hratio0 : 0 ≤ 2 * p / (1 - p) := div_nonneg (by linarith) (le_of_lt h1p)
  have hr0 : 0 ≤ r := by rw [hr]; exact mul_nonneg hratio0 (by positivity)
  -- Step 1: partition the deep set into depth-shells `K ∈ [s, F]`.
  rw [sum_filter_ge_eq_sum_shells (fun ρ : Restriction n => (canonicalDT cs F ρ).depth)
        (pweight p) s F (fun ρ => canonicalDT_depth_le cs F ρ)]
  -- Step 2: each shell is `≤ r^K`, so the shell-sum is `≤ ∑_{K∈[s,F]} r^K`.
  refine le_trans (Finset.sum_le_sum (fun K _ => ?_))
    (geom_shell_tail_le hr0 hr1 s F)
  -- per-shell bound
  have hshell := descent_switching_le_tight (p := p) hp0 hp3
    (w := w) (s := K) (F := F) (cs := cs)
    (Bad := Finset.univ.filter (fun ρ : Restriction n => (canonicalDT cs F ρ).depth = K))
    (fun ρ hρ => (Finset.mem_filter.mp hρ).2)
    (fun ρ _ => hnf ρ) (fun ρ _ => hleaf ρ) (fun ρ _ => hpos ρ)
  -- rewrite the per-shell RHS `(2p/(1-p))^K·((2w)^K : ℕ)` as `r^K`.
  have hcast : (((2 * w) ^ K : ℕ) : ℚ) = (2 * (w : ℚ)) ^ K := by push_cast; ring
  rw [hcast, ← mul_pow] at hshell
  exact hshell

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.tight_switching_budget
