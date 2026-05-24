import PallLean.Paper93.DeepMath.PathB.DynamicNFrameLagrangianInvariant

/-!
# Corrected paper-faithful dynamic N-frame/Lagrangian closure

This file proves the corrected observer-first route exactly as stated:

* P-side: polynomial dynamic CEW for the P observer class.
* SAT-side: dynamic N-frame/Lagrangian live-minor extraction.
* Bridge: operational observers are represented faithfully, so width is tied to
  actual trajectory states rather than arbitrary bookkeeping.

The SAT-side extraction theorem remains an input.  That is intentional: it is
the P-vs-NP-strength lower bound.  What is proved here is that these three
paper-faithful components close the observer separation criterion, and hence
rule out polynomial-width SAT observers in the corrected dynamic reading.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-! ## Corrected route package -/

/-- The corrected paper-faithful dynamic N-frame/Lagrangian route.

This is the exact replacement for the static SPDP-rank overclaim:
the P-side is dynamic CEW, the SAT-side is a live trajectory minor theorem,
and the bridge requires faithful operational presentation. -/
structure CorrectedDynamicNFrameLagrangianRoute
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop) : Prop where
  p_side : PaperMainPObserverCalibration PDecider
  faithful_bridge : PaperMainFaithfulObserverPresentation enc
  sat_live_minor :
    UniversalDynamicNFrameLagrangianExtraction enc

/-- The corrected route is definitionally the positive-program surface from
`DynamicNFrameLagrangianInvariant`. -/
def CorrectedDynamicNFrameLagrangianRoute.toPositiveProgram
    {enc : ThreeCNFEncoding}
    {PDecider : TrajectoryObserverMachine -> Prop}
    (route : CorrectedDynamicNFrameLagrangianRoute enc PDecider) :
    DynamicNFrameLagrangianPositiveProgram enc PDecider where
  p_side_dynamic_calibration := route.p_side
  faithful_presentation := route.faithful_bridge
  sat_dynamic_lagrangian_extraction := route.sat_live_minor

/-! ## Closure theorems -/

/-- The corrected route proves the paper-main observer separation criterion. -/
theorem paperMain_observerSeparationCriterion_of_correctedDynamicNFrameLagrangianRoute
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (route : CorrectedDynamicNFrameLagrangianRoute enc PDecider) :
    PaperMainObserverSeparationCriterion enc PDecider :=
  paperMain_observerSeparationCriterion_of_dynamicNFrameLagrangianProgram
    enc PDecider route.toPositiveProgram

/-- The corrected route proves the paper-main dynamic SAT lower bound. -/
theorem paperMain_dynamicSATLowerBound_of_correctedDynamicNFrameLagrangianRoute
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (route : CorrectedDynamicNFrameLagrangianRoute enc PDecider) :
    PaperMainDynamicSATLowerBound enc :=
  paperMain_dynamicSATLowerBound_of_dynamicNFrameLagrangianExtraction
    enc route.sat_live_minor route.faithful_bridge

/-- Consequently, the corrected route rules out a single operational SAT
observer of globally polynomial dynamic width. -/
theorem noUniformPolynomialWidthSATObserver_of_correctedDynamicNFrameLagrangianRoute
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (route : CorrectedDynamicNFrameLagrangianRoute enc PDecider) :
    NoUniformPolynomialWidthOperationalSATObserver enc :=
  noUniformPolynomialWidthOperationalSATObserver_of_dynamicSATLowerBound
    enc
    (paperMain_dynamicSATLowerBound_of_correctedDynamicNFrameLagrangianRoute
      enc PDecider route)

/-- SAT-side extraction alone already proves the faithful-class dynamic lower
bound.  This isolates the exact hard theorem from the easier P-side and
presentation bookkeeping. -/
theorem faithful_dynamicSATLowerBound_of_correctedSATLiveMinor
    (enc : ThreeCNFEncoding)
    (hextract : UniversalDynamicNFrameLagrangianExtraction enc) :
    DynamicCEW.NP_side_lower_bound
      (TrajectoryObserverWidths (FaithfulSATObserverClass enc)) :=
  faithful_dynamicSATLowerBound_of_dynamicNFrameLagrangianExtraction
    enc hextract

/-- If the P-side calibration and faithful bridge are available, then the
SAT-side live-minor theorem is the only remaining mathematical input. -/
theorem paperMain_observerSeparationCriterion_of_pSide_bridge_and_SATLiveMinor
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (hp : PaperMainPObserverCalibration PDecider)
    (hbridge : PaperMainFaithfulObserverPresentation enc)
    (hsat : UniversalDynamicNFrameLagrangianExtraction enc) :
    PaperMainObserverSeparationCriterion enc PDecider :=
  paperMain_observerSeparationCriterion_of_correctedDynamicNFrameLagrangianRoute
    enc PDecider
    { p_side := hp
      faithful_bridge := hbridge
      sat_live_minor := hsat }

/-! ## Kernel-only axiom trace -/

#print axioms paperMain_observerSeparationCriterion_of_correctedDynamicNFrameLagrangianRoute
#print axioms paperMain_dynamicSATLowerBound_of_correctedDynamicNFrameLagrangianRoute
#print axioms noUniformPolynomialWidthSATObserver_of_correctedDynamicNFrameLagrangianRoute
#print axioms faithful_dynamicSATLowerBound_of_correctedSATLiveMinor
#print axioms paperMain_observerSeparationCriterion_of_pSide_bridge_and_SATLiveMinor

end PallLean.Paper93.DeepMath.PathB
