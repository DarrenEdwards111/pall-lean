import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BoundedSurvival

/-!
# Bounded-overlap (disjoint-support) cell collapse — `FullACC0ForcesCellCollapse` discharged again

Continuing the attack on subcases of `FullACC0ForcesCellCollapse` (the N-Frame restriction lemma): this file handles
the **bounded-overlap** regime at its cleanest extreme — **pairwise-disjoint supports** (overlap `0`).  Unlike the
small-footprint case (`…ACC0BoundedSurvival`, which needs the supports to *leave room*, footprint `≤ n − 2`), this
works even when the supports cover *all* `n` variables — as long as one support is large.

The trick: take the live set `L =` one large support `S_{j₀}`.  Because the supports are disjoint, *no other* support
meets `S_{j₀}`, so exactly one survives (`survivingCount = 1`); and `2^1 = 2 < |S_{j₀}|` when `|S_{j₀}| ≥ 3`.  Collapse
holds, and the proved bridge gives the holonomy-correlation lower bound — *unconditionally*, no socket.

## What is proved (clean axioms, no `sorry`)

* **`disjoint_supports_forces_cellCollapse`** — pairwise-disjoint supports with some `|S_{j₀}| ≥ 3` ⇒
  `FullACC0ForcesCellCollapse` (live set `S_{j₀}`).
* **`disjoint_supports_low_holonomy_correlation`** — composing with the proved bridge (`nframe_route`): the predictor
  does not correlate with the holonomy parity, *unconditionally*.

## Honest scope — disjoint (overlap-0) only; degree-`d` overlap is *not* forced

This is the overlap-`0` (disjoint) subcase.  General bounded-overlap (each variable in `≤ d` supports, `d ≥ 2`) is
**not** forced into cell collapse by the overlap bound alone: a degree-`d` system has `≤ d·|L|` supports meeting any
live set `L`, and `2^{d·|L|} < |L|` is impossible — so on *no* large live set are there `< log₂|L|` survivors purely
from a degree bound.  Forcing collapse for `d ≥ 2` needs a genuine probabilistic restriction (the second-moment /
cell-bridge content socketed in `ACCSwitchingPipeline.bounded_overlap_acc0_low_correlation_whp`), which remains the
frontier.  So this proves the disjoint subcase exactly, and sharpens *why* mere overlap-`d` does not suffice.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DisjointCollapse

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACCSwitchingPipeline
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute

variable {n k : ℕ}

/-- **Disjoint supports force cell collapse (proved).**  If the supports are pairwise disjoint and some support
`S_{j₀}` has size `≥ 3`, then the live set `L = S_{j₀}` witnesses cell collapse: only `S_{j₀}` meets itself
(`survivingCount = 1`), and `2^1 = 2 < |S_{j₀}|`. -/
theorem disjoint_supports_forces_cellCollapse (supports : Fin k → Finset (Fin n))
    (hd : ∀ i j, i ≠ j → Disjoint (supports i) (supports j))
    (j₀ : Fin k) (hsize : 3 ≤ (supports j₀).card) :
    FullACC0ForcesCellCollapse supports := by
  refine ⟨supports j₀, ?_⟩
  -- only j₀ meets supports j₀, so the survivor filter is {j₀}
  have hfilter : (Finset.univ.filter (fun j => ¬ Disjoint (supports j) (supports j₀))) = {j₀} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hne
      exact hj (hd j j₀ hne)
    · intro hj
      rw [hj, Finset.not_disjoint_iff]
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (supports j₀).card)
      exact ⟨a, ha, ha⟩
  have hsurv : survivingCount supports (supports j₀) = 1 := by
    unfold survivingCount
    rw [hfilter, Finset.card_singleton]
  show 2 ^ survivingCount supports (supports j₀) < (supports j₀).card
  rw [hsurv, pow_one]
  omega

/-- **Unconditional low holonomy correlation for disjoint supports (proved).**  A predictor over pairwise-disjoint
supports with one support of size `≥ 3` does not correlate with the holonomy parity — the full N-Frame route, no
socket. -/
theorem disjoint_supports_low_holonomy_correlation (supports : Fin k → Finset (Fin n))
    (g : (Fin k → ℕ) → Bool) (hd : ∀ i j, i ≠ j → Disjoint (supports i) (supports j))
    (j₀ : Fin k) (hsize : 3 ≤ (supports j₀).card) :
    LowHolonomyCorrelation supports g :=
  nframe_route supports g (disjoint_supports_forces_cellCollapse supports hd j₀ hsize)

end PallLean.Paper93.DeepMath.PathB.ACC0DisjointCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DisjointCollapse.disjoint_supports_forces_cellCollapse
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DisjointCollapse.disjoint_supports_low_holonomy_correlation
