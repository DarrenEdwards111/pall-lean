import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RankCellCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ClusteredRank

/-!
# Block-diagonal MOD rank-shrink — `k` gates in `d` blocks ⇒ observer rank `≤ d`

A structured-`MOD` rank-shrink fragment.  Consider a wide layer of `k` `MOD` gates organised into `d` **blocks**, where
all gates in a block share the same support (each block computes one `MOD`/support over its region):

```
supports j = center (blk j)        (blk : Fin k → Fin d  the block of gate j,  center : Fin d → support).
```

Then every coordinate's cell pattern is determined by which of the `d` block-supports contain it, so the cell patterns
span at most `d` independent `F₂` directions:

```
cellRank supports L ≤ d        (the observer rank shrinks from `k` gates to `d` blocks),
2^d < |L|  ⇒  RankCellCollapse supports L  ⇒  low holonomy correlation.
```

This is a genuine rank-shrink (`d ≪ k`): the survivor count is `k`, but the *linear* observer rank is only `d`.  It is
the clustered fragment at variation rank `0`, packaged in the rank-cell API (`…ACC0RankCellCollapse`).

## What is proved (clean axioms, no `sorry`)

* `BlockEqualSupports` — `k` gates partitioned into `d` blocks of equal support.
* **`blockEqual_clustered`** — such a family is `ClusteredSupports … d 0`.
* **`blockEqual_cellRank_le`** — `cellRank supports L ≤ d`.
* **`blockEqual_rank_cell_collapse`** / **`blockEqual_low_correlation`** — `2^d < |L| ⇒ RankCellCollapse ⇒` low
  holonomy correlation.

## Honest scope

A structured rank-shrink fragment: it shrinks the observer rank to the block count for *block-equal* `MOD` layers (a
clean, genuine N-Frame observer theorem).  It does **not** force low rank for *general* wide overlapping `MOD` under a
restriction — that is the open rank-shrink wall (the rank analogue of the `MOD` no-absorbing-value wall).  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0BlockRankCollapse

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0CellCollapseRoute
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0ClusteredRank
open PallLean.Paper93.DeepMath.PathB.ACC0RankCellCollapse

variable {k n d : ℕ}

/-- **Block-equal supports**: `k` gates assigned to `d` blocks, all gates in a block sharing one support. -/
def BlockEqualSupports (supports : Fin k → Finset (Fin n)) (blk : Fin k → Fin d)
    (center : Fin d → Finset (Fin n)) : Prop :=
  ∀ j, supports j = center (blk j)

/-- **A block-equal layer is clustered with variation rank `0` (proved).** -/
theorem blockEqual_clustered (supports : Fin k → Finset (Fin n)) (blk : Fin k → Fin d)
    (center : Fin d → Finset (Fin n)) (h : BlockEqualSupports supports blk center) :
    ClusteredSupports supports d 0 := by
  refine ⟨fun a i => if i ∈ center a then (1 : ZMod 2) else 0, fun (_ : Fin 0) _ => 0,
          fun j a => if a = blk j then (1 : ZMod 2) else 0, fun j (_ : Fin 0) => 0, ?_⟩
  intro j i
  rw [h j]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [Finset.sum_eq_single (blk j)]
  · simp
  · intro a _ hane
    rw [if_neg hane, zero_mul]
  · intro hni
    exact absurd (Finset.mem_univ _) hni

/-- **Block-equal ⇒ observer rank `≤ d` (proved): the rank shrinks from `k` gates to `d` blocks.** -/
theorem blockEqual_cellRank_le (supports : Fin k → Finset (Fin n)) (blk : Fin k → Fin d)
    (center : Fin d → Finset (Fin n)) (h : BlockEqualSupports supports blk center)
    (L : Finset (Fin n)) : cellRank supports L ≤ d := by
  have hcl := clustered_supports_low_rank supports d 0 (blockEqual_clustered supports blk center h) L
  simpa using hcl

/-- **Block-equal rank-cell collapse (proved): `2^d < |L| ⇒ RankCellCollapse`.** -/
theorem blockEqual_rank_cell_collapse (supports : Fin k → Finset (Fin n)) (blk : Fin k → Fin d)
    (center : Fin d → Finset (Fin n)) (h : BlockEqualSupports supports blk center)
    (L : Finset (Fin n)) (hd : 2 ^ d < L.card) : RankCellCollapse supports L :=
  lt_of_le_of_lt
    (Nat.pow_le_pow_right (by norm_num) (blockEqual_cellRank_le supports blk center h L)) hd

/-- **Block-equal MOD layers fail to correlate when `2^d < |L|` (proved).**  The observer rank is only the block count
`d`, so the predictor cannot track the holonomy parity on a live set larger than `2^d`. -/
theorem blockEqual_low_correlation (supports : Fin k → Finset (Fin n)) (blk : Fin k → Fin d)
    (center : Fin d → Finset (Fin n)) (g : (Fin k → ℕ) → Bool)
    (h : BlockEqualSupports supports blk center) (L : Finset (Fin n)) (hd : 2 ^ d < L.card) :
    LowHolonomyCorrelation supports g :=
  rank_cell_collapse_implies_low_holonomy_correlation supports g L
    (blockEqual_rank_cell_collapse supports blk center h L hd)

end PallLean.Paper93.DeepMath.PathB.ACC0BlockRankCollapse

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BlockRankCollapse.blockEqual_clustered
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BlockRankCollapse.blockEqual_cellRank_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0BlockRankCollapse.blockEqual_low_correlation
