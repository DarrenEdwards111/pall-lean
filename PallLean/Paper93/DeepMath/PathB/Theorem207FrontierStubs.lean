import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGlobalGodMoveLowActionBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGlobalGodMoveCapacity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthStrictPortStandardBridge

/-!
# Theorem 207 frontier obligations

This file replaces the two former frontier axioms by strict prose→Lean
obligation records.

No new route is introduced here.  Each former stub is now a theorem whose proof
is just field-by-field unpacking of the corresponding obligation payload:

1. `strictObserverLowActionGodMoveCoverage_theorem`
2. `standardPvsNPBridge_instance`
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- One line of the C2 prose obligation for a fixed calibration exponent `c`
and strict observer `Ls`: exhibit the low-action representative, prove its
exponent is within the calibration, and prove pointwise equality of the live
boundary-rank trajectory. -/
structure StrictObserverLowActionGodMoveCoverageDatum
    (enc : ThreeCNFEncoding)
    (c : Nat)
    (Ls : StrictDynamicNFrameLagrangianObserver enc) : Type 1 where
  lowActionObserver : LowActionStrictDynamicNFrameLagrangianObserver enc
  lowActionExponent_le_calibration : lowActionObserver.k <= c
  liveBoundaryRank_eq :
    forall n : Nat,
      forall input : Fin n -> Bool,
      forall time : Nat,
        Ls.toTrajectory.liveBoundaryRank n input time =
          lowActionObserver.base.toTrajectory.liveBoundaryRank n input time

/-- C2 obligation package, exactly matching
`StrictObserverLowActionGodMoveCoverage`: every strict observer at every
calibration level has the datum above. -/
structure StrictObserverLowActionGodMoveCoverageObligations
    (enc : ThreeCNFEncoding) : Type 1 where
  coverageDatum :
    forall c : Nat,
      forall Ls : StrictDynamicNFrameLagrangianObserver enc,
        StrictObserverLowActionGodMoveCoverageDatum enc c Ls

/-- Frontier theorem C2, converted from prose into explicit Lean obligations.
The proof performs no route-building: it only repackages the obligation datum
into the already-defined coverage predicate. -/
theorem strictObserverLowActionGodMoveCoverage_theorem
    (enc : ThreeCNFEncoding)
    (O : StrictObserverLowActionGodMoveCoverageObligations enc) :
    StrictObserverLowActionGodMoveCoverage enc := by
  intro c Ls
  let d := O.coverageDatum c Ls
  exact ⟨d.lowActionObserver,
    d.lowActionExponent_le_calibration,
    d.liveBoundaryRank_eq⟩

/-- Derived full strict-class non-vacuous obstruction from C2. -/
theorem universalBook1BoundaryBudgetObstruction_of_provedCoverage
    (enc : ThreeCNFEncoding)
    (O : StrictObserverLowActionGodMoveCoverageObligations enc) :
    UniversalBook1BoundaryBudgetObstruction enc :=
  universalBook1BoundaryBudgetObstruction_of_lowActionGodMoveCoverage
    enc (strictObserverLowActionGodMoveCoverage_theorem enc O)

/-- Unconditional strict no-decider endpoint once C2 is supplied as obligations. -/
theorem no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_provedCoverage
    (enc : ThreeCNFEncoding)
    (O : StrictObserverLowActionGodMoveCoverageObligations enc)
    (Hport : Theorem207StrictLiveBoundaryPort enc) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) :=
  no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_lowActionGodMoveCoverage
    enc Hport (strictObserverLowActionGodMoveCoverage_theorem enc O)

/-- E2 obligation package for the intended standard model.  The bridge is split
into the proposition itself plus the two directions of equivalence with the
repository's encoded-DTM SAT lower-bound endpoint. -/
structure StandardPvsNPBridgeObligations
    (enc : ThreeCNFEncoding) : Type 1 where
  standardPvsNP : Prop
  standardPvsNP_implies_no_encodedSATDecider :
    standardPvsNP ->
      Not (exists M : TuringMachine.DTM,
        DTMDecidesSATWithEncoding enc M)
  no_encodedSATDecider_implies_standardPvsNP :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) ->
      standardPvsNP

/-- E2 bridge instance, converted from prose into explicit Lean obligations. -/
def standardPvsNPBridge_instance
    (enc : ThreeCNFEncoding)
    (O : StandardPvsNPBridgeObligations enc) :
    StandardPvsNPBridge enc where
  standardPvsNP := O.standardPvsNP
  standardPvsNP_iff_no_encodedSATDecider := by
    constructor
    · exact O.standardPvsNP_implies_no_encodedSATDecider
    · exact O.no_encodedSATDecider_implies_standardPvsNP

/-- Final exported standard statement from strict port + frontier obligations. -/
theorem standardPvsNP_of_theorem207StrictPort_and_frontier
    (enc : ThreeCNFEncoding)
    (Ostd : StandardPvsNPBridgeObligations enc)
    (Hport : Theorem207StrictLiveBoundaryPort enc) :
    (standardPvsNPBridge_instance enc Ostd).standardPvsNP :=
  standardPvsNP_of_theorem207StrictPort
    (standardPvsNPBridge_instance enc Ostd) Hport

/-- Final exported standard statement from strict port + both C2 and E2
obligation packages.  `Ocov` is present to expose the full frontier payload in
one theorem signature; the standard readout itself uses `Hport` plus `Ostd`. -/
theorem standardPvsNP_of_theorem207StrictPort_and_all_frontier_obligations
    (enc : ThreeCNFEncoding)
    (_Ocov : StrictObserverLowActionGodMoveCoverageObligations enc)
    (Ostd : StandardPvsNPBridgeObligations enc)
    (Hport : Theorem207StrictLiveBoundaryPort enc) :
    (standardPvsNPBridge_instance enc Ostd).standardPvsNP := by
  exact standardPvsNP_of_theorem207StrictPort_and_frontier enc Ostd Hport

#print axioms strictObserverLowActionGodMoveCoverage_theorem
#print axioms universalBook1BoundaryBudgetObstruction_of_provedCoverage
#print axioms no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_provedCoverage
#print axioms standardPvsNPBridge_instance
#print axioms standardPvsNP_of_theorem207StrictPort_and_frontier
#print axioms standardPvsNP_of_theorem207StrictPort_and_all_frontier_obligations

end PallLean.Paper93.DeepMath.PathB
