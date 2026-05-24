import PallLean.Paper93.DeepMath.PathB.FaithfulPACHolographyBridge

/-!
# Faithful closure wiring

This file performs only the final logical wiring for the faithful observer
route.  It does not prove the hard SAT lower bound.  Instead it packages the
three remaining obligations into one closure surface:

* P-side dynamic observer calibration;
* faithful presentation of operational SAT observers;
* PAC/holography-to-faithful-live-minor discharge.

Once those are supplied, the corrected paper-main observer separation criterion
follows mechanically.
-/

namespace PallLean.Paper93.DeepMath.PathB

/-- Final faithful paper-main closure package.

All three fields are genuine mathematical obligations.  The third field,
`live_minor_discharge`, is the load-bearing SAT lower-bound theorem: the
PAC/holography/amplituhedron/N-frame surface must produce live
`TrajectoryGodMoveBoundaryMinor`s for faithful SAT trajectories. -/
structure FaithfulPaperMainClosureWiring
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop) : Prop where
  p_side_calibration : PaperMainPObserverCalibration PDecider
  faithful_presentation : PaperMainFaithfulObserverPresentation enc
  live_minor_discharge : FaithfulPACHolographyLiveMinorDischarge enc

/-- The lower-bound half of the final wiring: faithful presentation plus the
PAC/holography live-minor discharge gives the paper-main dynamic SAT lower
bound. -/
theorem paperMain_dynamicSATLowerBound_of_faithfulClosureWiring
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (wiring : FaithfulPaperMainClosureWiring enc PDecider) :
    PaperMainDynamicSATLowerBound enc :=
  paperMain_dynamicSATLowerBound_of_faithfulGodMoveDCEWEngine
    enc
    (faithfulGodMoveDCEWEngine_of_PACHolographyLiveMinorDischarge
      enc wiring.faithful_presentation wiring.live_minor_discharge)

/-- Final paper-main observer separation criterion from the three faithful
wiring obligations. -/
theorem paperMain_observerSeparationCriterion_of_faithfulClosureWiring
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (wiring : FaithfulPaperMainClosureWiring enc PDecider) :
    PaperMainObserverSeparationCriterion enc PDecider :=
  ⟨wiring.p_side_calibration,
    paperMain_dynamicSATLowerBound_of_faithfulClosureWiring
      enc PDecider wiring⟩

/-- Consequence: the final wiring rules out a single uniformly polynomial-width
operational SAT observer.  This is weaker than the full dynamic lower bound,
but useful as an immediate corollary. -/
theorem noUniformPolynomialWidthOperationalSATObserver_of_faithfulClosureWiring
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (wiring : FaithfulPaperMainClosureWiring enc PDecider) :
    NoUniformPolynomialWidthOperationalSATObserver enc :=
  noUniformPolynomialWidthOperationalSATObserver_of_dynamicSATLowerBound
    enc
    (paperMain_dynamicSATLowerBound_of_faithfulClosureWiring
      enc PDecider wiring)

/-!
## Split-field closure theorems

These are convenience versions for use when the three obligations are proved in
separate files rather than bundled into `FaithfulPaperMainClosureWiring`.
-/

/-- Split-field version of the final observer separation criterion. -/
theorem paperMain_observerSeparationCriterion_of_faithfulFields
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (hp : PaperMainPObserverCalibration PDecider)
    (hpresent : PaperMainFaithfulObserverPresentation enc)
    (hdischarge : FaithfulPACHolographyLiveMinorDischarge enc) :
    PaperMainObserverSeparationCriterion enc PDecider :=
  paperMain_observerSeparationCriterion_of_faithfulClosureWiring
    enc PDecider
    ⟨hp, hpresent, hdischarge⟩

/-- Split-field version of the dynamic SAT lower bound. -/
theorem paperMain_dynamicSATLowerBound_of_faithfulFields
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (_hp : PaperMainPObserverCalibration PDecider)
    (hpresent : PaperMainFaithfulObserverPresentation enc)
    (hdischarge : FaithfulPACHolographyLiveMinorDischarge enc) :
    PaperMainDynamicSATLowerBound enc :=
  paperMain_dynamicSATLowerBound_of_faithfulClosureWiring
    enc PDecider
    ⟨_hp, hpresent, hdischarge⟩

#print axioms paperMain_dynamicSATLowerBound_of_faithfulClosureWiring
#print axioms paperMain_observerSeparationCriterion_of_faithfulClosureWiring
#print axioms noUniformPolynomialWidthOperationalSATObserver_of_faithfulClosureWiring
#print axioms paperMain_observerSeparationCriterion_of_faithfulFields
#print axioms paperMain_dynamicSATLowerBound_of_faithfulFields

end PallLean.Paper93.DeepMath.PathB
