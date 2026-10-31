import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityDepth3

/-!
# Tight switching, step 13: the tight budget is SATISFIABLE — the vacuity is removed (branch `razborov-recoverRho-wip`)

The concrete payoff of the tight route (bricks 50–52).  `depth3_budgets_unsatisfiable` proved that under the
crude `(4^w+1)^F` label count the depth-3 budget is *jointly unsatisfiable*: the fuel must exceed the
survivors (`n < F`), so the label count `≥ 2^F` forces the descent budget `s > F > n`, contradicting
`s ≤ k < n`.  That is exactly *why* `parity_not_depth3` was vacuous.

Here we exhibit a concrete parameter point at which the **`F`-independent tight threshold** — the *literal*
hypothesis `#gates · r^s/(1-r) < 1` (`r = (2p/(1-p))·(2w) = 4pw/(1-p)`) consumed by `tight_collapse_round`
(step 12) and `exists_shallow_all_tight` (step 11) — holds *together with* `s ≤ k < n`.  The witness
`p = 1/8, w = 1` (so `r = 4/7 < 1`), `#gates = 4`, `s = 5`, `k = 5`, `n = 100` gives
`4 · (4/7)^5/(3/7) = 28672/50421 ≈ 0.569 < 1`, with `5 ≤ 5 < 100`.

So the tight cap admits the regime `s ≤ k < n` that the crude cap *forbade*: the union-bound threshold is
`s ≳ log #gates` with no `F` anywhere, and there is room for `s` well below the survivor count `≈ p·n`.
This is the direct, numeric demonstration that the tight `(2w)^s` count removes the depth-3 vacuity — the
whole purpose of the tight route.

* `tight_round_budget_satisfiable` — concrete `p, w, s, k, n, G` with `0 ≤ p`, `3p ≤ 1`, `1 ≤ w`, `r < 1`,
  `G · r^s/(1-r) < 1`, and `s ≤ k < n`.

## Honest scope

This shows the *threshold* is satisfiable in the non-vacuous regime — the obstruction `depth3_budgets_un-`
`satisfiable` identified is gone.  Turning this into a closed `parity ∉ AC⁰` still needs the
`canonicalDT ↔ canonicalDTree` reconciliation (the tight count is over the single-literal tree `canonicalDT`;
the iteration spine `tower_not_parity`/`iterated_not_parity` needs block-tree `canonicalDTree` shallowness,
and `depth canonicalDTree ≥ depth canonicalDT` runs the wrong way for a free bridge).  That reconciliation —
a tight count over the block tree, or a parallel `canonicalDT`-based spine — is the remaining substantial
gate; we flag it honestly rather than claim a closed bound.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

/-- **The tight `F`-independent budget is satisfiable in the regime `s ≤ k < n`.**  A concrete parameter
point (`p = 1/8`, `w = 1`, `r = 4/7`, `#gates = 4`, `s = 5`, `k = 5`, `n = 100`) at which the literal
`tight_collapse_round` threshold `#gates · r^s/(1-r) < 1` holds *and* `s ≤ k < n` — the regime the crude
`(4^w+1)^F` cap proved impossible in `depth3_budgets_unsatisfiable`.  The vacuity is removed. -/
theorem tight_round_budget_satisfiable :
    ∃ (p : ℚ) (w s k n G : ℕ),
      0 ≤ p ∧ 3 * p ≤ 1 ∧ 1 ≤ w ∧
      (2 * p / (1 - p)) * (2 * (w : ℚ)) < 1 ∧
      (G : ℚ) * (((2 * p / (1 - p)) * (2 * (w : ℚ))) ^ s
          / (1 - (2 * p / (1 - p)) * (2 * (w : ℚ)))) < 1 ∧
      s ≤ k ∧ k < n := by
  refine ⟨1 / 8, 1, 5, 5, 100, 4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.tight_round_budget_satisfiable
