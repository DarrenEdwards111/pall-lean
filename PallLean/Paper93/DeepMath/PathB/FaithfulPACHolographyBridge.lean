import PallLean.Paper93.DeepMath.PathB.FaithfulTrajectoryObserver
import PallLean.PaperFaithfulSeparation
import PallLean.PAC
import PallLean.Paper93.NFrame.UnitPreservingValueSet

/-!
# Faithful PAC / holography bridge

This file connects the already-formalized PAC / holography / amplituhedron
surfaces to the faithful trajectory-observer socket.

The important point is deliberately explicit:

* if the geometric package supplies the operational trajectory extraction
  theorem, then it immediately supplies the faithful extraction theorem;
* the proven PAC rank-transport and unit-preserving N-frame selector surfaces
  are not, by themselves, the live-minor extraction theorem.  The missing
  discharge is exactly the theorem that this geometric data forces a
  `TrajectoryGodMoveBoundaryMinor` inside every faithful SAT trajectory.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation
open MultilinearSPDP

/-- Operational trajectory extraction immediately restricts to the faithful
SAT observer class. -/
theorem universalFaithfulExtraction_of_universalOperationalExtraction
    (enc : ThreeCNFEncoding)
    (hextract : UniversalOperationalTrajectorySATGodMoveExtraction enc) :
    UniversalFaithfulSATObserverGodMoveExtraction enc := by
  intro c
  rcases hextract c with ⟨n, hn20, hlog, hextract_at⟩
  refine ⟨n, hn20, hlog, ?_⟩
  intro T hfaithful
  exact hextract_at T
    (OperationalTrajectoryObserverDecidesSAT_of_faithful hfaithful)

/-- If PAC/holography/amplituhedron/Ramanujan supplies the operational
trajectory extraction theorem, and operational observers have faithful
presentations, then it supplies the faithful God-Move/DCEW engine. -/
theorem faithfulGodMoveDCEWEngine_of_NFramePACHolographyEngine
    (enc : ThreeCNFEncoding)
    (hpresent : PaperMainFaithfulObserverPresentation enc)
    (engine : NFramePACHolographyAmplituhedronRamanujanEngine enc) :
    FaithfulGodMoveDCEWEngine enc :=
  ⟨hpresent,
    universalFaithfulExtraction_of_universalOperationalExtraction
      enc engine.polytime_observer_extraction⟩

/-- Full paper-main observer separation from the faithful presentation
hypothesis and a PAC/holography/amplituhedron/Ramanujan operational extraction
engine. -/
theorem paperMain_observerSeparationCriterion_of_NFramePACHolographyEngine
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (hp : PaperMainPObserverCalibration PDecider)
    (hpresent : PaperMainFaithfulObserverPresentation enc)
    (engine : NFramePACHolographyAmplituhedronRamanujanEngine enc) :
    PaperMainObserverSeparationCriterion enc PDecider :=
  paperMain_observerSeparationCriterion_of_calibration_and_faithfulEngine
    enc PDecider hp
    (faithfulGodMoveDCEWEngine_of_NFramePACHolographyEngine
      enc hpresent engine)

/-- Safe PAC/holography rank-transport surface used by the faithful bridge. -/
def FaithfulHolographicPACBridgeSurface : Prop :=
  ∀ {N : ℕ} (B : SPDP.BlockPartition N) (κ ℓ : ℕ)
    (q : MvPolynomial (Fin N) ℚ)
    (π : PAC.Pipeline N)
    (rank_q_bound pipeline_factor_bound n_exp_target : ℕ),
    mlBlockedSpdpRank B (κ + PAC.Pipeline.κShiftSum π)
      (ℓ + PAC.Pipeline.ℓShiftSum π) q ≤ rank_q_bound →
    pipeline_factor_bound * rank_q_bound ≤ n_exp_target →
    N ^ PAC.Pipeline.factorSum π *
      mlBlockedSpdpRank B (κ + PAC.Pipeline.κShiftSum π)
        (ℓ + PAC.Pipeline.ℓShiftSum π) q ≤
    max (N ^ PAC.Pipeline.factorSum π * rank_q_bound)
        (pipeline_factor_bound * rank_q_bound) ∧
    mlBlockedSpdpRank B κ ℓ (PAC.applyPipeline π q) ≤
      N ^ PAC.Pipeline.factorSum π * rank_q_bound

/-- The existing PAC calculus proves the faithful bridge's rank-transport
surface. -/
theorem faithful_holographic_PAC_bridge :
    FaithfulHolographicPACBridgeSurface := by
  intro N B κ ℓ q π rank_q_bound pipeline_factor_bound n_exp_target hRankQ hExp
  exact PaperFaithfulSeparation.compiled_p_side_bound_from_PAC_pipeline
    B κ ℓ q π rank_q_bound pipeline_factor_bound n_exp_target hRankQ hExp

/-- Unit-preserving N-frame selector surface used by the faithful bridge. -/
def FaithfulUnitPreservingNFrameSelectorSurface : Prop :=
  ∀ {N : ℕ} (family : ℕ → MvPolynomial (Fin N) ℚ),
    ∃ Pi : PallLean.Paper93.NFrame.CandidateGauge N,
      PallLean.Paper93.NFrame.UnitPreservingAdmissibleGauge Pi ∧
      ∀ Pi' : PallLean.Paper93.NFrame.CandidateGauge N,
        PallLean.Paper93.NFrame.UnitPreservingAdmissibleGauge Pi' →
          PallLean.Paper93.NFrame.nframeLagrangian family Pi ≤
            PallLean.Paper93.NFrame.nframeLagrangian family Pi'

/-- The existing N-frame layer proves the faithful bridge's unit-preserving
selector surface. -/
theorem faithful_unitPreserving_nframe_selector :
    FaithfulUnitPreservingNFrameSelectorSurface := by
  intro N family
  exact PallLean.Paper93.NFrame.unitPreserving_minimizer_exists family

/-- The safe geometric surface currently available to the faithful bridge:
PAC rank transport plus the unit-preserving N-frame selector. -/
def FaithfulPACHolographyAmplituhedronNFrameSurface : Prop :=
  FaithfulHolographicPACBridgeSurface ∧
    FaithfulUnitPreservingNFrameSelectorSurface

/-- The currently available PAC/N-frame surface is proved, but it is only a
surface: it does not yet construct live trajectory minors. -/
theorem faithful_PAC_holography_amplituhedron_nframe_surface :
    FaithfulPACHolographyAmplituhedronNFrameSurface :=
  ⟨faithful_holographic_PAC_bridge,
    faithful_unitPreserving_nframe_selector⟩

/-- The exact missing PAC/holography-to-faithful-live-minor discharge.

The geometric surface gives PAC rank transport plus a unit-preserving N-frame
selector.  To close the faithful route, that surface must be upgraded to the
universal faithful trajectory extraction theorem: for every faithful
polynomial-time SAT trajectory, construct the live
`TrajectoryGodMoveBoundaryMinor`.
-/
def FaithfulPACHolographyLiveMinorDischarge
    (enc : ThreeCNFEncoding) : Prop :=
  FaithfulPACHolographyAmplituhedronNFrameSurface ->
    UniversalFaithfulSATObserverGodMoveExtraction enc

/-- The proven PAC/N-frame surface plus the live-minor discharge gives faithful
universal extraction. -/
theorem universalFaithfulExtraction_of_PACHolographyLiveMinorDischarge
    (enc : ThreeCNFEncoding)
    (hdischarge : FaithfulPACHolographyLiveMinorDischarge enc) :
    UniversalFaithfulSATObserverGodMoveExtraction enc :=
  hdischarge faithful_PAC_holography_amplituhedron_nframe_surface

/-- The faithful PAC live-minor discharge is exactly enough to build the
faithful God-Move/DCEW engine, once operational observers have faithful
presentations. -/
theorem faithfulGodMoveDCEWEngine_of_PACHolographyLiveMinorDischarge
    (enc : ThreeCNFEncoding)
    (hpresent : PaperMainFaithfulObserverPresentation enc)
    (hdischarge : FaithfulPACHolographyLiveMinorDischarge enc) :
    FaithfulGodMoveDCEWEngine enc :=
  ⟨hpresent,
    universalFaithfulExtraction_of_PACHolographyLiveMinorDischarge
      enc hdischarge⟩

/-- Full paper-main observer separation from the proven PAC/N-frame surface,
provided
the missing live-minor discharge and faithful-presentation theorem are supplied.
-/
theorem paperMain_observerSeparationCriterion_of_PACHolographyLiveMinorDischarge
    (enc : ThreeCNFEncoding)
    (PDecider : TrajectoryObserverMachine -> Prop)
    (hp : PaperMainPObserverCalibration PDecider)
    (hpresent : PaperMainFaithfulObserverPresentation enc)
    (hdischarge : FaithfulPACHolographyLiveMinorDischarge enc) :
    PaperMainObserverSeparationCriterion enc PDecider :=
  paperMain_observerSeparationCriterion_of_calibration_and_faithfulEngine
    enc PDecider hp
    (faithfulGodMoveDCEWEngine_of_PACHolographyLiveMinorDischarge
      enc hpresent hdischarge)

#print axioms universalFaithfulExtraction_of_universalOperationalExtraction
#print axioms faithfulGodMoveDCEWEngine_of_NFramePACHolographyEngine
#print axioms paperMain_observerSeparationCriterion_of_NFramePACHolographyEngine
#print axioms faithful_holographic_PAC_bridge
#print axioms faithful_unitPreserving_nframe_selector
#print axioms faithful_PAC_holography_amplituhedron_nframe_surface
#print axioms universalFaithfulExtraction_of_PACHolographyLiveMinorDischarge
#print axioms faithfulGodMoveDCEWEngine_of_PACHolographyLiveMinorDischarge
#print axioms paperMain_observerSeparationCriterion_of_PACHolographyLiveMinorDischarge

end PallLean.Paper93.DeepMath.PathB
