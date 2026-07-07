import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameConeAmplify

/-!
# N-Frame: the mixer's fresh charge is Θ(N), not Θ(N/d²) — Q1 answered, the fork collapses

A quantitative correction.  The claimed tension "mixer fresh ≈ N/d² may be too small to absorb the
sharing savings" rested on a factor-`d` miscalculation of the induced-matching size.  Re-derived
correctly, the fresh cut-rank is `Θ(N/d) = Θ(N)` for the constant degree `d` of a Ramanujan graph.

## The corrected chain

At a balanced cut of a `d`-regular Ramanujan graph:
  • EDGE EXPANSION gives `crossingEdges ≥ d·N/4` — a CONSTANT FRACTION of all `d·N/2` edges (the `d`
    was dropped in the earlier `N/d²` estimate).
  • GREEDY induced matching removes `≤ 2d²` crossing edges per matched edge (the edge, its `2d`
    endpoint-neighbours, and their `≤ d` incident edges), so `crossingEdges ≤ 2d²·matching`.

  `fresh_cut_rank_linear` — **PROVED**: from `d·N ≤ 4·crossingEdges` (expansion) and
        `crossingEdges ≤ 2·d·d·matching` (greedy), `N ≤ 8·d·matching` — i.e. the induced matching (and
        hence the fresh cut-rank) is `≥ N/(8d)`.  For constant `d` this is `Θ(N)`: `fresh = cN` with
        `c = 1/(8d)`, a constant.

## What this settles — and what it does not

Q1 ("can the mixer force fresh `Θ(N)` with `c ~ 1`?") is answered YES, already, by the ordinary
Ramanujan mixer with constant `d`.  The "fresh too small" tension DISSOLVES; the three-way fork
(increase fresh / decrease savings / stack deficits) collapses:
  • increase fresh — already done (`c = 1/(8d)` constant);
  • stack deficits — an all-middle circuit is self-consistent (linear `cbudget`), so `= the direct sum`;
so the ONLY remaining question is bounding the savings — `savings ≤ cN` — which is the cross-branch
direct sum / info-vs-size gap for this `F_k`.

Crucially, fresh `= Θ(N)` is NECESSARY but NOT SUFFICIENT: the cross-cone sharing happens BELOW the
mixer, on the disjoint inputs, so `savings` is decoupled from the mixer's fresh charge and can exceed
`cN` (a hard-low-info share routes few boundary bits yet skips an expensive sub-computation).  So this
corrects the record and reduces the fork to one question, but does NOT close the direct sum.  Nothing
here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameFreshLinear

/-- **THE CORRECTED FRESH BOUND (proved)**: given `d·N ≤ 4·crossingEdges` (edge expansion) and
`crossingEdges ≤ 2·d·d·matching` (greedy induced-matching blocking), the induced matching satisfies
`N ≤ 8·d·matching`, i.e. `matching ≥ N/(8d)`.  For constant `d` the fresh cut-rank is `Θ(N)`, not
`Θ(N/d²)`. -/
theorem fresh_cut_rank_linear (N d crossingEdges matching : ℕ) (hd : 1 ≤ d)
    (hcross : d * N ≤ 4 * crossingEdges)
    (hgreedy : crossingEdges ≤ 2 * d * d * matching) :
    N ≤ 8 * d * matching := by
  have key : d * N ≤ d * (8 * d * matching) := by nlinarith [hcross, hgreedy]
  exact Nat.le_of_mul_le_mul_left key hd

end PallLean.Paper93.DeepMath.PathB.NFrameFreshLinear

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameFreshLinear.fresh_cut_rank_linear
