import PallLean.Paper93.DeepMath.PathB.ComputationalDepthProfileCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLaneClassification

/-!
# Route F — the crossing-sequence rank bound (the reduction, proved)

The empirical `TMTableauTest` found the space-cut rank growing only ~linearly in depth.  The classical
*reason* is the **crossing-sequence method** (Hennie): everything the two sides of a space cut can "tell"
each other passes through the sequence of head-crossings at the boundary, so the communication rank is at
most the number of distinct crossing sequences.

This file formalizes that reduction and the polynomiality threshold it exposes.

## The reduction

A crossing sequence of `C` crossings over a size-`A` state-alphabet is an element of `Fin C → Fin A`, so
there are `A^C` of them (`crossingSeq_card`).  The space-cut communication rows **factor through** the
crossing-sequence interface (the structural content of Hennie's method), so by the proved lane principle
(`LaneClassification.profileCount_le_of_laneFactored`):

* `crossing_bound_general` — rank `≤ A^C` (always).
* `spaceCut_rank_poly_of_fewCrossings` — and if `C ≤ O(log n)`, then rank `≤ poly(n)`
  (via `ProfileCount.profile_count_le_poly`).

## Where the difficulty now lives (precisely)

The crossing count is the whole story:

* `C ≤ T` always (the head crosses at most once per step) — but that gives rank `≤ A^T`, **exponential**
  in `T`, hence `2^{poly(n)}`.  Useless.
* `C ≤ O(log n)` gives `poly(n)` — what Route F needs.

So **`CookLevinFrontierHyp` (P-side) reduces to a single precise, falsifiable claim: the head crosses the
relevant cut `O(log n)` times.**  This is **false for general Turing machines** (an arbitrary `T`-time
machine can cross a fixed boundary `Θ(T)` times), so it is *not* a generic fact — it must come from the
specific structure of the Cook–Levin *compilation* (an oblivious / few-crossing layout, or the paper's SPDP
partition chosen so crossings are few).  That structural claim is the genuine open content.

`TMTableauTest`'s ~linear-in-depth measurement is consistent with *few effective* crossing sequences for that
concrete machine; the open theorem is that crossings stay `O(log n)` for **every** bounded compilation —
which no finite test settles, and which an adversarial machine could violate.  Nothing here asserts it.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingBound

open PallLean.Paper93.DeepMath.PathB

/-- The number of crossing sequences of `C` crossings, each labelled from a size-`A` state-alphabet, is
`A^C`. -/
theorem crossingSeq_card (A C : ℕ) : Fintype.card (Fin C → Fin A) = A ^ C := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- **Crossing-sequence rank bound (general).**  If the space-cut communication rows factor through the
crossing-sequence interface (Hennie's method), the rank (= number of distinct rows) is `≤ A^C`.  With the
trivial `C ≤ T` this is `A^T` — exponential. -/
theorem crossing_bound_general {NC A C : ℕ} {Row : Type*} [DecidableEq Row]
    (rows : Fin NC → Row) (csIndex : Fin NC → Fin (A ^ C))
    (hfactor : LaneClassification.LaneFactored rows csIndex) :
    (Finset.univ.image rows).card ≤ A ^ C :=
  LaneClassification.profileCount_le_of_laneFactored rows csIndex hfactor

/-- **Crossing-sequence rank reduction (polynomial case).**  If the rows factor through the crossing
sequences (`hfactor`) **and** the head crosses the cut `C ≤ O(log n)` times (`hFew`, the open structural
claim), then the space-cut rank is `≤ poly(n)`. -/
theorem spaceCut_rank_poly_of_fewCrossings {NC A c n C : ℕ} {Row : Type*} [DecidableEq Row]
    (hA : 1 ≤ A) (hn : 1 ≤ n) (hFew : C ≤ c * Nat.log 2 n)
    (rows : Fin NC → Row) (csIndex : Fin NC → Fin (A ^ C))
    (hfactor : LaneClassification.LaneFactored rows csIndex) :
    (Finset.univ.image rows).card ≤ n ^ (c * (Nat.log 2 A + 1)) := by
  calc (Finset.univ.image rows).card
      ≤ A ^ C := crossing_bound_general rows csIndex hfactor
    _ ≤ A ^ (c * Nat.log 2 n) := Nat.pow_le_pow_right hA hFew
    _ ≤ n ^ (c * (Nat.log 2 A + 1)) := ProfileCount.profile_count_le_poly A c n hn

end PallLean.Paper93.DeepMath.PathB.CrossingBound

#print axioms PallLean.Paper93.DeepMath.PathB.CrossingBound.spaceCut_rank_poly_of_fewCrossings
