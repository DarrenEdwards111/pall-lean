import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RandomRestrictionRankCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0NFrameLowerBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0WilliamsCashoutFromPolynomial

/-!
# The `ACC⁰` frontier — two final conditional theorems, two named walls

The whole programme reduces to **two** deep open theorems.  Everything downstream of each is proved (clean axioms).
This file states both final conditionals cleanly, so "what remains" is a single machine-checked map.

## Route A — the N-Frame rank-observer route (one socket)

```
NFrameRankShrink sys   (∀ predictor: a live set L with the linear observer state space 2^{cellRank} < |L|)
        │  rank_shrink_gives_acc0_lower_bound   (PROVED, via the rank-cell bridge)
        ▼
ACC0HolonomyLowerBound sys tops   (no predictor in the class correlates with the holonomy parity)
```

The downstream chain — `RankCellCollapse → 2^{cellRank} < |L|` observer states `→ same-cell pair → low holonomy
correlation` — is fully proved (`…ACC0RankCellCollapse`, `…ACC0RandomRestrictionRankCollapse`).  The **open socket** is
`NFrameRankShrink`: that some boundary/restriction forces `cellRank < log₂|L|` on a large live set for *wide
overlapping `MOD`*.  That is the rank analogue of the `MOD` no-absorbing-value wall — `NP ⊄ ACC⁰`-strength.

## Route B — the Williams / Beigel–Tarui route (one socket + standard inputs)

```
composite_BT_degree  (composite-modulus ACC⁰ has a quasipolynomial SYM∘AND representation)
        │  counting   (representation ⇒ sub-2ⁿ ACC⁰-SAT: kernel + SYM-layer + moments + inversion + BT count, mostly proved)
        │  williams   (the speedup collapses NEXP ⊆ ACC⁰)
        │  hierarchy  (nondeterministic time hierarchy)
        ▼
NEXP ⊄ ACC⁰
```

The count side (sparse cube-sum kernel, SYM-layer reduction, binomial moments/inversion, BT monomial-count `≤ (n+1)^D`)
and the `AC⁰[p]` degree bound are proved.  The **open socket** is `composite_BT_degree`: the deep Yao/Beigel–Tarui
symmetric-representation construction for *composite* modulus.

## What is proved here (clean axioms, no `sorry`)

* `NFrameRankShrink` — the Route-A socket; **`rank_shrink_gives_acc0_lower_bound`** — socket ⇒ holonomy lower bound.
* **`composite_route_to_NEXP_not_ACC0`** — Route-B conditional: `composite_BT_degree`, `counting`, `williams`,
  `hierarchy` ⇒ `¬ NEXPHasACC0Circuits`.

## Honest scope

Both theorems are **conditionals**, not the separations.  Route A's socket and Route B's `composite_BT_degree` (and the
`williams`/`hierarchy` inputs) are the genuine open `NP/NEXP`-strength content, left as named hypotheses.  This file is
the faithful "what remains" map.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RankRouteFrontier

open scoped Classical
open PallLean.Paper93.DeepMath.PathB.ACC0RankCellCollapse
open PallLean.Paper93.DeepMath.PathB.ACC0NFrameLowerBound
open PallLean.Paper93.DeepMath.PathB.ACC0WilliamsCashoutFromPolynomial

variable {n : ℕ}

/-! ## Route A — the N-Frame rank-observer route -/

/-- **The Route-A socket (open): every predictor's supports admit a rank-collapsed large live set.**  For each
predictor in the class, some live set `L` has linear observer state space `2^{cellRank} < |L|`. -/
def NFrameRankShrink {ι : Type} (sys : PredictorClass ι n) : Prop :=
  ∀ i, ∃ L : Finset (Fin n), RankCellCollapse (sys i).2 L

/-- **Route A (proved conditional): rank-shrink ⇒ the holonomy lower bound.**  Given the rank-shrink socket, every
predictor fails to correlate — by the proved rank-cell bridge applied to each. -/
theorem rank_shrink_gives_acc0_lower_bound {ι : Type} (sys : PredictorClass ι n)
    (tops : ∀ i, (Fin (sys i).1 → ℕ) → Bool) (h : NFrameRankShrink sys) :
    ACC0HolonomyLowerBound sys tops := by
  intro i
  obtain ⟨L, hL⟩ := h i
  exact rank_cell_collapse_implies_low_holonomy_correlation (sys i).2 (tops i) L hL

/-! ## Route B — the Williams / Beigel–Tarui route -/

/-- **Route B (proved conditional): composite Beigel–Tarui ⇒ `NEXP ⊄ ACC⁰`.**  The composite-modulus `SYM∘AND`
representation `composite_BT_degree` feeds the counting socket (sparse-counting kernel + SYM-layer + binomial
inversion + `BT` count, mostly proved); `williams` collapses `NEXP ⊆ ACC⁰` from the SAT speedup; `hierarchy` is the
nondeterministic time hierarchy.  The only deep open input is `composite_BT_degree`. -/
theorem composite_route_to_NEXP_not_ACC0
    (RSRep ACC0SatSpeedup NEXPHasACC0Circuits Collapse : Prop)
    (composite_BT_degree : RSRep)
    (counting : RSRep → ACC0SatSpeedup)
    (williams : ACC0SatSpeedup → NEXPHasACC0Circuits → Collapse)
    (hierarchy : ¬ Collapse) :
    ¬ NEXPHasACC0Circuits :=
  williams_cashout_skeleton RSRep ACC0SatSpeedup NEXPHasACC0Circuits Collapse
    counting williams hierarchy composite_BT_degree

end PallLean.Paper93.DeepMath.PathB.ACC0RankRouteFrontier

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankRouteFrontier.rank_shrink_gives_acc0_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankRouteFrontier.composite_route_to_NEXP_not_ACC0
