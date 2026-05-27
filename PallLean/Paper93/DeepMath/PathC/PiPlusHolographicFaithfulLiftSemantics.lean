import PallLean.Paper93.DeepMath.PathC.PiPlusHolographicBoundaryBulkPivot

/-!
# Faithful holographic lift semantics

`PiPlusHolographicBoundaryBulkPivot` deliberately separates the P-side
boundary rank from the NP-side bulk rank.  Its remaining load-bearing field is

```lean
faithful_boundary_to_bulk :
  DecidesSAT M -> bulk.rank <= liftCost boundary.rank
```

This file replaces that raw inequality with a concrete finite decoder
semantics.  A SAT-deciding observer is required to provide an injective coding
of bulk rank witnesses into the finite code space made available by the
2D boundary lift.  The rank inequality is then a theorem by finite cardinality,
not an assumed rank comparison.

This matches the Book-1 holographic reading: a finite observer boundary can
faithfully reconstruct only the bulk degrees of freedom that can be encoded
through its boundary interface.  It still does not prove that every SAT decider
has such a decoder; that is the remaining Cook-Levin/observer-semantics target.
-/

namespace PallLean.Paper93.DeepMath.PathC

open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- Faithful boundary/bulk lift as an actual finite code.

The type `Fin bulk.rank` represents independent bulk witnesses/minor rows.
The type `Fin (liftCost boundary.rank)` represents the finite code space that
the boundary projection can lift into the bulk.  Faithfulness is injectivity:
distinct bulk witnesses cannot collapse to the same boundary-lift code. -/
structure BoundaryBulkFaithfulDecoder
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (boundary : HolographicBoundaryLayer M n hn2 htb hns)
    (bulk : HolographicBulkLayer M n hn2 htb hns)
    (liftCost : Nat -> Nat) where
  encodeBulkWitness :
    Fin bulk.rank -> Fin (liftCost boundary.rank)
  encodeBulkWitness_injective :
    Function.Injective encodeBulkWitness

/-- The raw faithful-holography inequality follows from faithful finite
decoding by cardinality. -/
theorem faithful_boundary_to_bulk_of_decoder
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {boundary : HolographicBoundaryLayer M n hn2 htb hns}
    {bulk : HolographicBulkLayer M n hn2 htb hns}
    {liftCost : Nat -> Nat}
    (D : BoundaryBulkFaithfulDecoder boundary bulk liftCost) :
    bulk.rank <= liftCost boundary.rank := by
  simpa [Fintype.card_fin] using
    (Fintype.card_le_of_injective D.encodeBulkWitness
      D.encodeBulkWitness_injective)

/-- Pre-pivot data where faithful holography is supplied as decoder semantics,
not as the already-compressed rank inequality. -/
structure HolographicBoundaryBulkDecoderPivotData
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) where
  boundary : HolographicBoundaryLayer M n hn2 htb hns
  bulk : HolographicBulkLayer M n hn2 htb hns
  liftCost : Nat -> Nat
  liftCost_mono : Monotone liftCost

  /-- P-side: polynomial capacity bound on the 2D boundary only. -/
  boundary_P_bound : boundary.rank <= n ^ 200

  /-- NP-side: a SAT decider forces a binomial-rank identity minor in the bulk. -/
  bulk_NP_lower : DecidesSAT M -> Nat.choose (n / 3) (Nat.log 2 n) <= bulk.rank

  /-- Book-1 faithful reconstruction: a SAT decider supplies an injective
  boundary-lift code for the independent bulk witnesses. -/
  faithful_decoder :
    DecidesSAT M ->
      BoundaryBulkFaithfulDecoder boundary bulk liftCost

  /-- Capacity gap: even the lift of a polynomial 2D boundary budget is too
  small to carry the bulk NP minor. -/
  holographic_gap : liftCost (n ^ 200) < Nat.choose (n / 3) (Nat.log 2 n)

/-- Promote decoder-based data into the earlier pivot data by deriving the
faithful boundary-to-bulk inequality from the decoder. -/
def HolographicBoundaryBulkDecoderPivotData.toPivotData
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (D : HolographicBoundaryBulkDecoderPivotData M n hn2 htb hns) :
    HolographicBoundaryBulkPivotData M n hn2 htb hns where
  boundary := D.boundary
  bulk := D.bulk
  liftCost := D.liftCost
  liftCost_mono := D.liftCost_mono
  boundary_P_bound := D.boundary_P_bound
  bulk_NP_lower := D.bulk_NP_lower
  faithful_boundary_to_bulk := fun hdec =>
    faithful_boundary_to_bulk_of_decoder (D.faithful_decoder hdec)
  holographic_gap := D.holographic_gap

/-- Decoder-based holographic contradiction.  This is the same separated
boundary/bulk endpoint, but the lift leg is now discharged from a faithful
finite decoder. -/
theorem no_decidesSAT_of_holographicBoundaryBulkDecoderPivotData
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (D : HolographicBoundaryBulkDecoderPivotData M n hn2 htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_of_holographicBoundaryBulkPivotData
    M n hn2 htb hns D.toPivotData

/-- Paper-scale wrapper for decoder-based holographic data. -/
abbrev PaperScaleHolographicBoundaryBulkDecoderPivotData
    (M : DTM) (htb : M.timeBound <= 4)
    (hns : M.numStates <= 2 ^ 804) :=
  HolographicBoundaryBulkDecoderPivotData M (2 ^ 804)
    projectedPivot_paperScale_ge_two htb hns

/-- Paper-scale no-decider endpoint from decoder-based data. -/
theorem no_decidesSAT_at_paperScale_of_holographicBoundaryBulkDecoderPivotData
    (M : DTM) (htb : M.timeBound <= 4)
    (hns : M.numStates <= 2 ^ 804)
    (D : PaperScaleHolographicBoundaryBulkDecoderPivotData M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_of_holographicBoundaryBulkDecoderPivotData
    M (2 ^ 804) projectedPivot_paperScale_ge_two htb hns D

/-! ## Axiom audit anchors -/

#print axioms faithful_boundary_to_bulk_of_decoder
#print axioms HolographicBoundaryBulkDecoderPivotData.toPivotData
#print axioms no_decidesSAT_of_holographicBoundaryBulkDecoderPivotData
#print axioms no_decidesSAT_at_paperScale_of_holographicBoundaryBulkDecoderPivotData

end PallLean.Paper93.DeepMath.PathC
