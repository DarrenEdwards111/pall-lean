import PallLean.Paper93.DeepMath.PathC.PiPlusHolographicFaithfulLiftSemantics

/-!
# Kill-test for the faithful holographic decoder premise

This file tests the remaining Path C premise against what a SAT-deciding
machine can actually expose on the 2D boundary.

The previous file proved that an injective `BoundaryBulkFaithfulDecoder` is
exactly the cardinal lift inequality.  Here we make the boundary-exposed code
space explicit.  If a decider exposes only `exposedCodeCount` boundary codes,
and those codes fit inside the holographic lift capacity, then any faithful
bulk decoder through the exposed data promotes to the previous decoder.

Consequently:

* under the boundary/bulk gap, no SAT-deciding machine can have such an exposed
  faithful decoder;
* in particular, a zero/constant/degenerate boundary exposure with positive
  bulk rank cannot have one.

This is the intended kill-test: the faithful-lift premise survives only if one
can prove, from real machine semantics, a nondegenerate exposed boundary code
space large enough to inject all independent bulk witnesses.  The zero-rank
case is formally refuted here.
-/

namespace PallLean.Paper93.DeepMath.PathC

open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- What the SAT decider actually exposes on the 2D boundary, abstracted to a
finite code count.  The field `exposed_le_lift` says these are genuinely
boundary-lift codes, not hidden bulk data smuggled in. -/
structure SATDeciderBoundaryCodeExposure
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (boundary : HolographicBoundaryLayer M n hn2 htb hns)
    (liftCost : Nat -> Nat) where
  exposedCodeCount : Nat
  exposed_le_lift : exposedCodeCount <= liftCost boundary.rank

/-- Faithful decoder using only the codes actually exposed on the 2D boundary. -/
structure BoundaryExposedFaithfulDecoder
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {boundary : HolographicBoundaryLayer M n hn2 htb hns}
    (bulk : HolographicBulkLayer M n hn2 htb hns)
    {liftCost : Nat -> Nat}
    (exposure : SATDeciderBoundaryCodeExposure boundary liftCost) where
  encodeBulkWitness : Fin bulk.rank -> Fin exposure.exposedCodeCount
  encodeBulkWitness_injective : Function.Injective encodeBulkWitness

/-- Any decoder through actually exposed boundary codes promotes to the previous
boundary/bulk faithful decoder, because exposed codes are a subcapacity of the
holographic lift code space. -/
def BoundaryExposedFaithfulDecoder.toBoundaryBulkFaithfulDecoder
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {boundary : HolographicBoundaryLayer M n hn2 htb hns}
    {bulk : HolographicBulkLayer M n hn2 htb hns}
    {liftCost : Nat -> Nat}
    {exposure : SATDeciderBoundaryCodeExposure boundary liftCost}
    (D : BoundaryExposedFaithfulDecoder bulk exposure) :
    BoundaryBulkFaithfulDecoder boundary bulk liftCost where
  encodeBulkWitness := fun i =>
    ⟨(D.encodeBulkWitness i).val,
      Nat.lt_of_lt_of_le (D.encodeBulkWitness i).isLt exposure.exposed_le_lift⟩
  encodeBulkWitness_injective := by
    intro i j hij
    apply D.encodeBulkWitness_injective
    apply Fin.ext
    exact congrArg (fun x : Fin (liftCost boundary.rank) => x.val) hij

/-- Exposed faithful decoding is therefore at least as strong as the cardinal
lift inequality. -/
theorem faithful_boundary_to_bulk_of_exposed_decoder
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {boundary : HolographicBoundaryLayer M n hn2 htb hns}
    {bulk : HolographicBulkLayer M n hn2 htb hns}
    {liftCost : Nat -> Nat}
    {exposure : SATDeciderBoundaryCodeExposure boundary liftCost}
    (D : BoundaryExposedFaithfulDecoder bulk exposure) :
    bulk.rank <= liftCost boundary.rank :=
  faithful_boundary_to_bulk_of_decoder D.toBoundaryBulkFaithfulDecoder

/-- Gap kill-test: under the same boundary P-bound, bulk NP-lower, and
holographic gap, no SAT-deciding machine can have a faithful decoder using only
its actually exposed 2D boundary codes. -/
theorem no_exposed_decoder_of_boundary_bulk_gap
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {boundary : HolographicBoundaryLayer M n hn2 htb hns}
    {bulk : HolographicBulkLayer M n hn2 htb hns}
    {liftCost : Nat -> Nat}
    {exposure : SATDeciderBoundaryCodeExposure boundary liftCost}
    (liftCost_mono : Monotone liftCost)
    (boundary_P_bound : boundary.rank <= n ^ 200)
    (bulk_NP_lower :
      DecidesSAT M -> Nat.choose (n / 3) (Nat.log 2 n) <= bulk.rank)
    (holographic_gap :
      liftCost (n ^ 200) < Nat.choose (n / 3) (Nat.log 2 n))
    (hdec : DecidesSAT M) :
    Not (Nonempty (BoundaryExposedFaithfulDecoder bulk exposure)) := by
  intro hD
  rcases hD with ⟨D⟩
  exact no_decoder_of_boundary_bulk_gap
    liftCost_mono boundary_P_bound bulk_NP_lower holographic_gap hdec
    ⟨D.toBoundaryBulkFaithfulDecoder⟩

/-- Zero-lift kill-test: if the boundary lift code space is empty but the bulk
has a positive-rank minor, no faithful boundary/bulk decoder exists. -/
theorem no_decoder_of_zero_boundary_lift
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {boundary : HolographicBoundaryLayer M n hn2 htb hns}
    {bulk : HolographicBulkLayer M n hn2 htb hns}
    {liftCost : Nat -> Nat}
    (hbulk_pos : 0 < bulk.rank)
    (hzero_lift : liftCost boundary.rank = 0) :
    Not (Nonempty (BoundaryBulkFaithfulDecoder boundary bulk liftCost)) := by
  intro hD
  have hlift : bulk.rank <= liftCost boundary.rank :=
    (exists_decoder_iff_faithful_boundary_to_bulk).mp hD
  rw [hzero_lift] at hlift
  exact Nat.not_lt_of_ge hlift hbulk_pos

/-- Zero-exposure kill-test: a constant/degenerate boundary exposure carrying no
codes cannot faithfully encode a positive-rank bulk minor. -/
theorem no_exposed_decoder_of_zero_exposure
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {boundary : HolographicBoundaryLayer M n hn2 htb hns}
    {bulk : HolographicBulkLayer M n hn2 htb hns}
    {liftCost : Nat -> Nat}
    {exposure : SATDeciderBoundaryCodeExposure boundary liftCost}
    (hbulk_pos : 0 < bulk.rank)
    (hzero_exposed : exposure.exposedCodeCount = 0) :
    Not (Nonempty (BoundaryExposedFaithfulDecoder bulk exposure)) := by
  intro hD
  rcases hD with ⟨D⟩
  have hcard : bulk.rank <= exposure.exposedCodeCount := by
    simpa [Fintype.card_fin] using
      (Fintype.card_le_of_injective D.encodeBulkWitness
        D.encodeBulkWitness_injective)
  rw [hzero_exposed] at hcard
  exact Nat.not_lt_of_ge hcard hbulk_pos

/-- Concrete degenerate exposure constructor: no boundary codes are exposed. -/
def zeroBoundaryCodeExposure
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (boundary : HolographicBoundaryLayer M n hn2 htb hns)
    (liftCost : Nat -> Nat)
    (hzero_le : 0 <= liftCost boundary.rank := Nat.zero_le _) :
    SATDeciderBoundaryCodeExposure boundary liftCost where
  exposedCodeCount := 0
  exposed_le_lift := hzero_le

@[simp] theorem zeroBoundaryCodeExposure_count
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (boundary : HolographicBoundaryLayer M n hn2 htb hns)
    (liftCost : Nat -> Nat)
    (hzero_le : 0 <= liftCost boundary.rank := Nat.zero_le _) :
    (zeroBoundaryCodeExposure boundary liftCost hzero_le).exposedCodeCount = 0 := rfl

/-- Degenerate-exposure verdict: positive bulk rank formally refutes the idea
that a zero/constant 2D boundary can supply the faithful decoder. -/
theorem no_exposed_decoder_of_zeroBoundaryCodeExposure
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    {boundary : HolographicBoundaryLayer M n hn2 htb hns}
    {bulk : HolographicBulkLayer M n hn2 htb hns}
    {liftCost : Nat -> Nat}
    (hbulk_pos : 0 < bulk.rank) :
    Not (Nonempty (BoundaryExposedFaithfulDecoder bulk
      (zeroBoundaryCodeExposure boundary liftCost))) := by
  exact no_exposed_decoder_of_zero_exposure hbulk_pos rfl

/-! ## Axiom audit anchors -/

#print axioms BoundaryExposedFaithfulDecoder.toBoundaryBulkFaithfulDecoder
#print axioms faithful_boundary_to_bulk_of_exposed_decoder
#print axioms no_exposed_decoder_of_boundary_bulk_gap
#print axioms no_decoder_of_zero_boundary_lift
#print axioms no_exposed_decoder_of_zero_exposure
#print axioms zeroBoundaryCodeExposure
#print axioms no_exposed_decoder_of_zeroBoundaryCodeExposure

end PallLean.Paper93.DeepMath.PathC
