import PallLean.Paper93.DeepMath.PathB.ObserverTrajectoryDCEW

/-!
# Paper-main faithful DCEW reading

This module aligns the observer/DCEW Lean route with the controlling correction
paragraph in `paper/main.tex` on the `godmove-paper-faithful` branch:

* dynamic CEW is the observer-width quantity used for the separation criterion;
* static SPDP rank is only an algebraic diagnostic/local lower-bound proxy;
* the missing theorem is the SAT observer-width lower bound;
* the paper-scale `timeBound <= 4` route proves the full dynamic lower bound
  only when paired with an explicit normalization from arbitrary polynomial
  time to that paper-scale class.

No separation theorem is asserted here without the corresponding lower-bound
or normalization hypotheses.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-- The paper-main SAT observer class: DTM-backed trajectory observers deciding
SAT under the chosen encoding. -/
abbrev PaperMainSATObserverClass
    (enc : ThreeCNFEncoding) : TrajectoryObserverMachine -> Prop :=
  OperationalTrajectoryObserverDecidesSAT enc

/-- The exact dynamic SAT lower bound named in the paper correction paragraph:
`DCEW_SAT(n) \not\le n^{O(1)}`. -/
abbrev PaperMainDynamicSATLowerBound (enc : ThreeCNFEncoding) : Prop :=
  DynamicCEW.NP_side_lower_bound
    (TrajectoryObserverWidths (PaperMainSATObserverClass enc))

/-- P-side dynamic observer calibration for an arbitrary P-observer class. -/
abbrev PaperMainPObserverCalibration
    (PDecider : TrajectoryObserverMachine -> Prop) : Prop :=
  DynamicCEW.P_side_bound (TrajectoryObserverWidths PDecider)

/-- The paper-main observer separation criterion, stated as the conjunction of
P-side dynamic calibration and SAT dynamic lower bound. -/
abbrev PaperMainObserverSeparationCriterion
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop) : Prop :=
  DynamicCEW.WouldYieldSeparation
    (TrajectoryObserverWidths PDecider)
    (TrajectoryObserverWidths (PaperMainSATObserverClass enc))

/-- A global polynomial-width SAT observer, as a single observer whose width is
bounded by one exponent at every length.  This is weaker than the dynamic CEW
lower bound, but it is often the informal target when discussing
polynomial-time observers. -/
def NoUniformPolynomialWidthOperationalSATObserver
    (enc : ThreeCNFEncoding) : Prop :=
  forall c : Nat,
    Not (TrajectoryObserverSATPolyWidthAtMost
      (PaperMainSATObserverClass enc) c)

/-- The dynamic SAT lower bound rules out a single global polynomial-width SAT
observer.  This records the quantifier direction: DCEW lower bound is the
stronger paper-level target. -/
theorem noUniformPolynomialWidthOperationalSATObserver_of_dynamicSATLowerBound
    (enc : ThreeCNFEncoding)
    (hlower : PaperMainDynamicSATLowerBound enc) :
    NoUniformPolynomialWidthOperationalSATObserver enc := by
  intro c hpoly
  rcases hpoly with ⟨T, hdec, hwidth⟩
  rcases hlower c with ⟨n, hnot⟩
  have hcew :
      DynamicCEW.DCEWatMost
        (TrajectoryObserverWidths (PaperMainSATObserverClass enc)) n (n ^ c) := by
    exact ⟨T.width, ⟨T, hdec, rfl⟩, hwidth n⟩
  exact hnot hcew

/-- The exact God-Move/DCEW engine needed by the corrected paper-main observer
route.  The single field is the hard theorem: every operational SAT trajectory
exposes the high-rank live boundary minor at the required scales. -/
structure PaperMainFaithfulGodMoveDCEWEngine
    (enc : ThreeCNFEncoding) : Prop where
  universal_live_boundary_extraction :
    UniversalOperationalTrajectorySATGodMoveExtraction enc

/-- The paper-main faithful God-Move/DCEW engine discharges the dynamic SAT
lower bound. -/
theorem paperMain_dynamicSATLowerBound_of_godMoveDCEWEngine
    (enc : ThreeCNFEncoding)
    (engine : PaperMainFaithfulGodMoveDCEWEngine enc) :
    PaperMainDynamicSATLowerBound enc :=
  NP_side_lower_bound_of_universalOperationalTrajectorySATGodMoveExtraction
    enc engine.universal_live_boundary_extraction

/-- With the P-side dynamic calibration, the faithful God-Move/DCEW engine gives
the paper-main observer separation criterion. -/
theorem paperMain_observerSeparationCriterion_of_calibration_and_engine
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (hp : PaperMainPObserverCalibration PDecider)
    (engine : PaperMainFaithfulGodMoveDCEWEngine enc) :
    PaperMainObserverSeparationCriterion enc PDecider :=
  ⟨hp, paperMain_dynamicSATLowerBound_of_godMoveDCEWEngine enc engine⟩

/-- The paper-scale Route-B/R72 normal form: every operational SAT trajectory
observer can be represented by one whose backing DTM has `timeBound <= 4`.

This is a hypothesis here.  Without it, the paper-scale `timeBound <= 4`
extraction only proves the lower bound for that bounded subclass, not for all
polynomial-time observers. -/
def PaperMainTimeBoundFourNormalization
    (enc : ThreeCNFEncoding) : Prop :=
  forall T : TrajectoryObserverMachine,
    OperationalTrajectoryObserverDecidesSAT enc T ->
      OperationalTrajectoryObserverDecidesSATAtMost enc 4 T

/-- Paper-scale extraction alone proves the dynamic lower bound for the
`timeBound <= 4` subclass. -/
theorem paperMain_boundedTimeDynamicSATLowerBound_of_paperScaleExtraction
    (enc : ThreeCNFEncoding)
    (hextract : PaperScaleOperationalTrajectorySATGodMoveExtraction enc) :
    DynamicCEW.NP_side_lower_bound
      (TrajectoryObserverWidths
        (OperationalTrajectoryObserverDecidesSATAtMost enc 4)) :=
  NP_side_lower_bound_of_paperScaleOperationalTrajectorySATGodMoveExtraction
    enc hextract

/-- Paper-scale extraction becomes the full paper-main dynamic SAT lower bound
only after an explicit `timeBound <= 4` normalization step. -/
theorem paperMain_dynamicSATLowerBound_of_paperScaleExtraction_and_normalization
    (enc : ThreeCNFEncoding)
    (hextract : PaperScaleOperationalTrajectorySATGodMoveExtraction enc)
    (hnorm : PaperMainTimeBoundFourNormalization enc) :
    PaperMainDynamicSATLowerBound enc := by
  intro c
  rcases
    paperMain_boundedTimeDynamicSATLowerBound_of_paperScaleExtraction
      enc hextract c with
    ⟨n, hnot_bounded⟩
  refine ⟨n, ?_⟩
  intro hcew
  rcases hcew with ⟨w, hw_decides, hw_bound⟩
  rcases hw_decides with ⟨T, hdec, hwidth_eq⟩
  exact hnot_bounded
    ⟨w, ⟨T, hnorm T hdec, hwidth_eq⟩, hw_bound⟩

/-- The time-exponent-parametric engine rules out a single global polynomial
width SAT observer, but this is intentionally stated separately from the full
dynamic CEW lower bound because the extraction length may depend on the
machine's time exponent. -/
theorem paperMain_noUniformPolynomialWidth_of_timeExponentParametricEngine
    (enc : ThreeCNFEncoding)
    (engine :
      TimeExponentParametricNFramePACHolographyAmplituhedronRamanujanEngine enc) :
    NoUniformPolynomialWidthOperationalSATObserver enc := by
  intro c
  exact not_polyWidthOperationalSATObserver_of_timeExponentParametricEngine
    enc engine c

#print axioms paperMain_dynamicSATLowerBound_of_godMoveDCEWEngine
#print axioms paperMain_dynamicSATLowerBound_of_paperScaleExtraction_and_normalization
#print axioms paperMain_noUniformPolynomialWidth_of_timeExponentParametricEngine

end PallLean.Paper93.DeepMath.PathB
