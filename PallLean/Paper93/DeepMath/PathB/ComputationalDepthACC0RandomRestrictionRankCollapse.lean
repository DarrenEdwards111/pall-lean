import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RankCellCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RankWhp

/-!
# Random restriction yields a `RankCellCollapse` witness

The random-restriction rank route already proves low correlation from the two-event rank tail
(`…ACC0RankWhp.rank_predictor_fails_whp`) and from an expected-survivor bound
(`…ACC0RandomRestrictionRank.randomRestriction_forces_low_cellRank`).  This file exposes the intermediate
**`RankCellCollapse` witness** in the new rank-cell API: the probabilistic method produces a *specific large live set
`L` on which the observer state space `2^{cellRank}` is below `|L|`* — making the "low-rank incidence on a live set"
content explicit rather than only its correlation consequence.

```
2^a ≤ b,   Pr[cellRank ≥ a] + Pr[|L| ≤ b] < 1   ⇒   ∃ L,  RankCellCollapse supports L   ⇒   low correlation.
```

## What is proved (clean axioms, no `sorry`)

* **`exists_rankCellCollapse_whp`** — the two-event balance yields a live set with `RankCellCollapse supports L`
  (`2^{cellRank} < |L|`), i.e. the linear observer has fewer than `|L|` states on `L`.
* **`randomRestriction_rank_collapse_low_correlation`** — hence low holonomy correlation (via the rank-cell bridge).

## Honest scope

This packages the probabilistic rank route into the `RankCellCollapse`/observer-state-space API; it is the rank
analogue of the cell-count whp, keyed on the *cell-rank* tail (sharper than the survivor tail, since
`cellRank ≤ survivingCount`).  The load-bearing input — the feasibility `Pr[cellRank ≥ a] + Pr[|L| ≤ b] < 1` for wide
overlapping `MOD` — is exactly the open rank-shrink balance (the rank analogue of the `MOD` no-absorbing-value wall): a
restriction simultaneously low-rank (`cellRank < a`) and large (`|L| > b ≥ 2^a`).  Not established here for adversarial
`MOD`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionRankCollapse

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingChebyshev
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0RankCellCollapse

variable {k n : ℕ}

/-- **The probabilistic method yields a `RankCellCollapse` witness (proved).**  If `2^a ≤ b` and the rank tail plus the
small-live tail sum to `< 1`, some live set is simultaneously low-rank (`cellRank < a`) and large (`|L| > b ≥ 2^a`), so
`2^{cellRank} < |L|` — the linear observer has fewer than `|L|` states on `L`. -/
theorem exists_rankCellCollapse_whp (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (a b : ℕ) (hab : 2 ^ a ≤ b)
    (hfeas : Pr p (fun L => a ≤ cellRank supports L)
        + Pr p (fun L : Finset (Fin n) => L.card ≤ b) < 1) :
    ∃ L ∈ (Finset.univ : Finset (Fin n)).powerset, RankCellCollapse supports L := by
  obtain ⟨L, hL, hnot1, hnot2⟩ := exists_both_of_pr_add_lt_one p hp0 hp1
    (fun L : Finset (Fin n) => a ≤ cellRank supports L)
    (fun L : Finset (Fin n) => L.card ≤ b) hfeas
  push_neg at hnot1 hnot2
  refine ⟨L, hL, ?_⟩
  show 2 ^ cellRank supports L < L.card
  calc 2 ^ cellRank supports L < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) hnot1
    _ ≤ b := hab
    _ < L.card := hnot2

/-- **Random restriction ⇒ low holonomy correlation, via the rank-cell witness (proved).** -/
theorem randomRestriction_rank_collapse_low_correlation (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (supports : Fin k → Finset (Fin n)) (g : (Fin k → ℕ) → Bool) (a b : ℕ) (hab : 2 ^ a ≤ b)
    (hfeas : Pr p (fun L => a ≤ cellRank supports L)
        + Pr p (fun L : Finset (Fin n) => L.card ≤ b) < 1) :
    LowHolonomyCorrelation supports g := by
  obtain ⟨L, _, hcollapse⟩ := exists_rankCellCollapse_whp p hp0 hp1 supports a b hab hfeas
  exact rank_cell_collapse_implies_low_holonomy_correlation supports g L hcollapse

end PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionRankCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionRankCollapse.exists_rankCellCollapse_whp
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RandomRestrictionRankCollapse.randomRestriction_rank_collapse_low_correlation
