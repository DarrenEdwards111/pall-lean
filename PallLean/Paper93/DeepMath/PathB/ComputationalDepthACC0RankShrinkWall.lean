import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RankCellCollapse

/-!
# The rank-shrink wall is real — `NFrameRankShrink` is *false* for the membership-rank observer

The N-Frame frontier (`…ACC0RankRouteFrontier`) left one Route-A socket: `NFrameRankShrink`, that a restriction forces
`2^{cellRank} < |L|` on a large live set for arbitrary `ACC⁰` supports.  Attacking it honestly means first asking
whether it is *true*.  It is **not** — for the membership-rank observer it is a genuine barrier, not a provable lemma.

**Why.**  `cellRank supports L` is the `F₂`-rank of the (live-set-independent) *membership* incidence; restriction only
*drops* coordinates.  And `RankCellCollapse` forces a **pattern collision** (two live coordinates with equal membership
patterns).  But adversarial `ACC⁰`-realizable supports — the *singletons* `supports j = {j}` (each gate reads one
variable) — have **injective** patterns (`cellPatternVec v = Pi.single v 1`), so no collision ever occurs and
`RankCellCollapse` is impossible on every live set.  Hence `NFrameRankShrink` is false for this `ACC⁰` family.

## What is proved (clean axioms, no `sorry`)

* **`rankCellCollapse_implies_collision`** — `RankCellCollapse ⇒` two live coordinates share a membership pattern (the
  collapse *needs* a collision).
* **`not_rankCellCollapse_of_injOn`** — injective patterns on `L` ⇒ `¬ RankCellCollapse` (`|L| ≤ 2^{cellRank}`).
* **`singleton_supports_injective`** — the singleton family has injective patterns.
* **`singleton_supports_no_rank_collapse`** — `∀ L, ¬ RankCellCollapse (singletons) L`: a concrete `ACC⁰`-realizable
  family on which the rank observer **never** collapses, refuting `NFrameRankShrink`.

## Honest conclusion — the right resolution is the polynomial-method rank, not the observer rank

The *membership-rank* observer cannot cross the wall: rank-shrink demands pattern collisions, which adversarial supports
defeat (matching the cell-count characterization `…ACC0CellCountCharacterization` and the `MOD` no-go).  The rank notion
that *does* separate is the **polynomial-method effective dimension** (the low-degree evaluation span `V_D`, which the
holonomy parity escapes — `…ACC0PivotToPolynomialMethod`), not the observer incidence rank.  So Route A's wall is a true
barrier for the observer route, and the working route is Route B (the polynomial method).  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0RankShrinkWall

open scoped Classical
open Finset
open PallLean.Paper93.DeepMath.PathB.ACC0RankBridge
open PallLean.Paper93.DeepMath.PathB.ACC0RankCellCollapse

variable {k n : ℕ}

/-- **Rank-shrink needs a collision (proved): `RankCellCollapse ⇒` two live coordinates share a pattern.** -/
theorem rankCellCollapse_implies_collision (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (h : RankCellCollapse supports L) :
    ∃ v ∈ L, ∃ w ∈ L, v ≠ w ∧ cellPatternVec supports v = cellPatternVec supports w := by
  obtain ⟨v, hv, w, hw, hne, hcell⟩ := exists_sameCell_pair_of_rank supports L h
  exact ⟨v, hv, w, hw, hne, (sameCell_iff_pattern supports v w).mp hcell⟩

/-- **Injective patterns ⇒ no rank collapse (proved): `|L| ≤ 2^{cellRank}`.** -/
theorem not_rankCellCollapse_of_injOn (supports : Fin k → Finset (Fin n)) (L : Finset (Fin n))
    (hinj : Set.InjOn (cellPatternVec supports) (↑L : Set (Fin n))) :
    ¬ RankCellCollapse supports L := by
  unfold RankCellCollapse
  push_neg
  calc L.card = (L.image (cellPatternVec supports)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ 2 ^ cellRank supports L := cellPattern_image_card_le supports L

/-- **The singleton family has injective patterns (proved): `cellPatternVec v = Pi.single v 1`.** -/
theorem singleton_supports_injective :
    Function.Injective (cellPatternVec (fun j : Fin n => ({j} : Finset (Fin n)))) := by
  intro v w hvw
  have hj := congrFun hvw v
  by_cases h : w = v
  · exact h.symm
  · exfalso
    simp only [cellPatternVec, Finset.mem_singleton] at hj
    rw [if_neg h] at hj
    simp at hj

/-- **The rank observer never collapses on the singleton family (proved): `NFrameRankShrink` is false here.**  Each
gate reads one variable (`ACC⁰`-realizable), patterns are the distinct standard basis vectors, so `RankCellCollapse`
fails on every live set — refuting the Route-A socket for this support system. -/
theorem singleton_supports_no_rank_collapse (L : Finset (Fin n)) :
    ¬ RankCellCollapse (fun j : Fin n => ({j} : Finset (Fin n))) L :=
  not_rankCellCollapse_of_injOn _ L (singleton_supports_injective.injOn)

end PallLean.Paper93.DeepMath.PathB.ACC0RankShrinkWall

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankShrinkWall.rankCellCollapse_implies_collision
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankShrinkWall.not_rankCellCollapse_of_injOn
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankShrinkWall.singleton_supports_injective
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0RankShrinkWall.singleton_supports_no_rank_collapse
