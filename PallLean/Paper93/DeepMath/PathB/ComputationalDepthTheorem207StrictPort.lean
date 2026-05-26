import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGlobalGodMoveLiveBoundaryBridge
import PallLean.Paper93.DeepMath.PathB.StrictFaithfulGodMoveDCEWEngine
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTheorem207DirectPaperPort

/-!
# Theorem 207 -> strict live-boundary port surface

This file makes the remaining Route-B obligation explicit in the exact form
required by the strict dynamic observer route.

The key point is to treat the port target as a first-class theorem statement:

`UniversalStrictDynamicNFrameLagrangianExtraction enc`.

Everything downstream (strict DCEW lower bound + paper-main observer separation)
then composes without touching the older source/transport rank sandwich.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Canonical name for the remaining hard theorem:
port paper-faithful Route-B content into strict live-boundary extraction. -/
abbrev Theorem207StrictLiveBoundaryPort
    (enc : ThreeCNFEncoding) : Prop :=
  UniversalStrictDynamicNFrameLagrangianExtraction enc

/-- The strict paper-bridge alias is exactly the strict port target. -/
theorem theorem207StrictPort_iff_globalGodMovePaperBridgeStrict
    (enc : ThreeCNFEncoding) :
    Theorem207StrictLiveBoundaryPort enc <->
      GlobalGodMovePaperBridgeStrict enc := by
  rfl

/-- Once the strict port theorem is available, the strict extraction route
for strict faithful observers is immediate. -/
theorem strictTrajectoryExtraction_of_theorem207StrictPort
    (enc : ThreeCNFEncoding)
    (Hport : Theorem207StrictLiveBoundaryPort enc) :
    UniversalTrajectorySATGodMoveExtraction enc (StrictFaithfulSATObserverClass enc) :=
  strictUniversalExtraction_of_globalGodMovePaperBridge enc Hport

/-- Package-level constructor: a strict port theorem plus strict presentation
builds the strict DCEW engine consumed by the paper-main route. -/
def strictFaithfulGodMoveDCEWEngine_of_theorem207StrictPort
    (enc : ThreeCNFEncoding)
    (hpresent : PaperMainStrictFaithfulObserverPresentation enc)
    (Hport : Theorem207StrictLiveBoundaryPort enc) :
    StrictFaithfulGodMoveDCEWEngine enc where
  strict_faithful_presentation := hpresent
  strict_live_boundary_extraction := Hport

/-- End-to-end strict Route-B closure from the port theorem. -/
theorem paperMain_observerSeparationCriterion_of_theorem207StrictPort
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (hp : PaperMainPObserverCalibration PDecider)
    (hpresent : PaperMainStrictFaithfulObserverPresentation enc)
    (Hport : Theorem207StrictLiveBoundaryPort enc) :
    PaperMainObserverSeparationCriterion enc PDecider :=
  paperMain_observerSeparationCriterion_of_calibration_and_strictFaithfulEngine
    enc PDecider hp
    (strictFaithfulGodMoveDCEWEngine_of_theorem207StrictPort
      enc hpresent Hport)

/-- Obstruction-side closure in strict theorem shape. -/
theorem no_theorem207StrictLiveBoundaryPort_of_nonemptyObserver_and_universalBook1Obstruction
    (enc : ThreeCNFEncoding)
    (hL : Nonempty (StrictDynamicNFrameLagrangianObserver enc))
    (Hobs : UniversalBook1BoundaryBudgetObstruction enc) :
    Not (Theorem207StrictLiveBoundaryPort enc) :=
  no_universalStrictDynamicNFrameLagrangianExtraction_of_nonemptyObserver_and_universalBook1Obstruction
    enc hL Hobs

#print axioms theorem207StrictPort_iff_globalGodMovePaperBridgeStrict
#print axioms strictTrajectoryExtraction_of_theorem207StrictPort
#print axioms strictFaithfulGodMoveDCEWEngine_of_theorem207StrictPort
#print axioms paperMain_observerSeparationCriterion_of_theorem207StrictPort
#print axioms no_theorem207StrictLiveBoundaryPort_of_nonemptyObserver_and_universalBook1Obstruction

end PallLean.Paper93.DeepMath.PathB
