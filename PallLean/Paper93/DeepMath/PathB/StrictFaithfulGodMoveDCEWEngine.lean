import PallLean.Paper93.DeepMath.PathB.StrictDynamicNFrameLagrangianInvariant
import PallLean.Paper93.DeepMath.PathB.FaithfulTrajectoryObserver

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Strict presentation hypothesis: every operational SAT observer has a strict
full-configuration faithful presentation. -/
def PaperMainStrictFaithfulObserverPresentation
    (enc : ThreeCNFEncoding) : Prop :=
  forall T : TrajectoryObserverMachine,
    OperationalTrajectoryObserverDecidesSAT enc T ->
      StrictFaithfulSATObserverClass enc T

/-- Strict extraction implies NP-side lower bound for the strict faithful class. -/
theorem strict_dynamicSATLowerBound_of_universalStrictDynamicNFrameLagrangianExtraction
    (enc : ThreeCNFEncoding)
    (hextract : UniversalStrictDynamicNFrameLagrangianExtraction enc) :
    DynamicCEW.NP_side_lower_bound
      (TrajectoryObserverWidths (StrictFaithfulSATObserverClass enc)) :=
  NP_side_lower_bound_of_universalTrajectorySATGodMoveExtraction
    enc (StrictFaithfulSATObserverClass enc)
    (strictFaithfulExtraction_of_universalStrictDynamicNFrameLagrangianExtraction
      enc hextract)

/-- Strict-class lower bound upgrades to paper-main lower bound under strict
presentation. -/
theorem paperMain_dynamicSATLowerBound_of_strictLowerBound_and_presentation
    (enc : ThreeCNFEncoding)
    (hlower :
      DynamicCEW.NP_side_lower_bound
        (TrajectoryObserverWidths (StrictFaithfulSATObserverClass enc)))
    (hpresent : PaperMainStrictFaithfulObserverPresentation enc) :
    PaperMainDynamicSATLowerBound enc := by
  intro c
  rcases hlower c with ⟨n, hnot_strict⟩
  refine ⟨n, ?_⟩
  intro hcew
  rcases hcew with ⟨w, hw_decides, hw_bound⟩
  rcases hw_decides with ⟨T, hdec, hwidth_eq⟩
  exact hnot_strict
    ⟨w, ⟨T, hpresent T hdec, hwidth_eq⟩, hw_bound⟩

/-- Strict full-configuration God-Move engine: strict presentation + strict
universal extraction. -/
structure StrictFaithfulGodMoveDCEWEngine
    (enc : ThreeCNFEncoding) : Prop where
  strict_faithful_presentation :
    PaperMainStrictFaithfulObserverPresentation enc
  strict_live_boundary_extraction :
    UniversalStrictDynamicNFrameLagrangianExtraction enc

/-- Strict engine discharges paper-main dynamic SAT lower bound. -/
theorem paperMain_dynamicSATLowerBound_of_strictFaithfulGodMoveDCEWEngine
    (enc : ThreeCNFEncoding)
    (engine : StrictFaithfulGodMoveDCEWEngine enc) :
    PaperMainDynamicSATLowerBound enc :=
  paperMain_dynamicSATLowerBound_of_strictLowerBound_and_presentation
    enc
    (strict_dynamicSATLowerBound_of_universalStrictDynamicNFrameLagrangianExtraction
      enc engine.strict_live_boundary_extraction)
    engine.strict_faithful_presentation

/-- With P-side calibration, strict engine yields the paper-main observer
separation criterion. -/
theorem paperMain_observerSeparationCriterion_of_calibration_and_strictFaithfulEngine
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (hp : PaperMainPObserverCalibration PDecider)
    (engine : StrictFaithfulGodMoveDCEWEngine enc) :
    PaperMainObserverSeparationCriterion enc PDecider :=
  ⟨hp,
    paperMain_dynamicSATLowerBound_of_strictFaithfulGodMoveDCEWEngine
      enc engine⟩

#print axioms strict_dynamicSATLowerBound_of_universalStrictDynamicNFrameLagrangianExtraction
#print axioms paperMain_dynamicSATLowerBound_of_strictFaithfulGodMoveDCEWEngine
#print axioms paperMain_observerSeparationCriterion_of_calibration_and_strictFaithfulEngine

end PallLean.Paper93.DeepMath.PathB
