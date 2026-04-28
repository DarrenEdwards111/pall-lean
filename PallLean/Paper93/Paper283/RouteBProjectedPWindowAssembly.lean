import PallLean.Paper93.Paper283.RouteBZeroProfileProjectedPWindowProgress
import PallLean.Paper93.Paper283.RouteBProjectionRetargetProgress

/-!
# Route B projected P-window assembly

This file connects the quotiented zero-profile projected P-window bridge to
the corrected PiPhi/head-span Route B path.

The remaining P-side content is deliberately the projected containment
statement for the selected PiPhi/head-span gauge.  No conversion back to
`CookLevinZeroHistogramShiftCommonSpan` or to an unprojected P-window cover is
used here.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open TuringMachine
open PaperFaithfulSeparation
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The small arithmetic envelope needed by the projected zero-profile bridge:
the single within-profile budget at `κ = log₂ n` fits under the paper-scale
`n^200` P-side allowance. -/
theorem routeB_withinProfileBound_log_le_pow_200
    (n : Nat) (hn2 : n >= 2) :
    withinProfileBound (Nat.log 2 n) <= n ^ 200 := by
  rw [WithinProfileBound.withinProfileBound_eq_pow8]
  have hbase : Nat.log 2 n + 1 <= 2 * n := by
    have hlog : Nat.log 2 n <= n := Nat.log_le_self 2 n
    omega
  calc
    (Nat.log 2 n + 1) ^ 8 <= (2 * n) ^ 8 :=
      Nat.pow_le_pow_left hbase 8
    _ = 2 ^ 8 * n ^ 8 := by ring
    _ <= n ^ 192 * n ^ 8 := by
      apply Nat.mul_le_mul_right
      calc
        (2 : Nat) ^ 8 = 256 := by norm_num
        _ <= 2 ^ 192 := by norm_num
        _ <= n ^ 192 := by
          exact Nat.pow_le_pow_left hn2 192
    _ = n ^ 200 := by ring

/-- Minimal projected containment needed for the quotiented zero-profile span
to control the PiPhi/head-span projected P-window.

This is the only new P-side hypothesis left after the checked quotiented
zero-profile common-span target is supplied. -/
def RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat) : Prop :=
  RouteBProjectedPWindowControlledByZeroProfileProjection
    M n hn2 htb hns project
    (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns)

/-- Concrete projected P-side constructor for the PiPhi/head-span gauge from
the quotiented zero-profile target plus the narrow projected containment
hypothesis above. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_projectedPSideBound_of_zeroProfileQuotientedShiftCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (hquot :
      CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn2 htb hns project)
    (hcontrol :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns) := by
  simpa [RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection,
    routeBPaperFaithfulPiPhiHeadSpanProjection] using
    routeBRicherGauge_projectedPSideBound_of_zeroProfileQuotientedShiftCommonSpan
      M n hn2 htb hns project
      (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns)
      hquot hcontrol
      (routeB_withinProfileBound_log_le_pow_200 n hn2)

/-- PiPhi/head-span SAT subgoals from direct SPDP containment, the projected
zero-profile P-side constructor, and the existing projected NP bridge. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_routeBNFrameGaugeSubgoals_of_zeroProfileQuotientedShiftCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (hspdp :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns))
    (hquot :
      CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn2 htb hns project)
    (hcontrol :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project)
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)) :
    RouteBNFrameGaugeSubgoals M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      satDeciderGaugeRankMonotonicity_of_spdpSubspaceImageContainment
        M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
        (routeBRicherGauge_spdpImageContainment_of_subspaceContainment
          M n hn2 htb hns
          (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns)
          hspdp)
  · exact
      routeBPaperFaithfulPiPhiHeadSpan_projectedPSideBound_of_zeroProfileQuotientedShiftCommonSpan
        M n hn2 htb hns project hquot hcontrol
  · exact
      satDeciderGaugeNPIdentityMinorPreservation_of_projected_compiled_lower_bound
        M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
        (routeBPaperFaithfulPiPhiHeadSpan_projectedNPIdentityMinorLowerBound_of_source
          M n hn2 htb hns hsource)

/-- Retargeted PiPhi/head-span version of the same SAT subgoal assembly.  The
retarget package supplies SPDP map-preimage, while the P-side remains the
projected zero-profile containment named above. -/
theorem routeBPaperFaithfulPiPhiHeadSpan_routeBNFrameGaugeSubgoals_of_retarget_zeroProfileQuotientedShiftCommonSpan
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (retarget :
      RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
        M n hn2 htb hns)
    (hquot :
      CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn2 htb hns project)
    (hcontrol :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project)
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)) :
    RouteBNFrameGaugeSubgoals M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns) := by
  apply
    routeBPaperFaithfulPiPhiHeadSpan_routeBNFrameGaugeSubgoals_of_zeroProfileQuotientedShiftCommonSpan
      M n hn2 htb hns project
  · simpa [routeBPaperFaithfulPiPhiHeadSpanGauge] using
      routeBRicherFiniteRowsCandidateGauge_spdpSubspaceContainment_of_mapPreimage
        M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanRows M n hn2 htb hns)
        (routeBPaperFaithfulPiPhiHeadSpan_spdpMapPreimage_of_retarget
          M n hn2 htb hns retarget)
  · exact hquot
  · exact hcontrol
  · exact hsource

/-- Direct final-target assembly for the PiPhi/head-span gauge using the
projected zero-profile P-side path. -/
theorem cookLevinRichProjectionTarget_of_PiPhiHeadSpan_zeroProfileQuotientedShiftCommonSpan
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (hspdp :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns))
    (hquot :
      CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn2 htb hns project)
    (hcontrol :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project)
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_routeBNFrameGaugeSubgoals
    M n hn hn2 htb hns
    (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns)
    (routeBPaperFaithfulPiPhiHeadSpan_routeBNFrameGaugeSubgoals_of_zeroProfileQuotientedShiftCommonSpan
      M n hn2 htb hns project hspdp hquot hcontrol hsource)

/-- Final-target assembly with SPDP containment supplied by the retargeted
PiPhi/head-span package. -/
theorem cookLevinRichProjectionTarget_of_PiPhiHeadSpan_retarget_zeroProfileQuotientedShiftCommonSpan
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (retarget :
      RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
        M n hn2 htb hns)
    (hquot :
      CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn2 htb hns project)
    (hcontrol :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project)
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (routeBRicherConcreteNPWitnessQ M n hn2 htb hns)) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_routeBNFrameGaugeSubgoals
    M n hn hn2 htb hns
    (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns)
    (routeBPaperFaithfulPiPhiHeadSpan_routeBNFrameGaugeSubgoals_of_retarget_zeroProfileQuotientedShiftCommonSpan
      M n hn2 htb hns project retarget hquot hcontrol hsource)

/-! ## Axiom audit anchors -/

#print axioms routeB_withinProfileBound_log_le_pow_200
#print axioms RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection
#print axioms routeBPaperFaithfulPiPhiHeadSpan_projectedPSideBound_of_zeroProfileQuotientedShiftCommonSpan
#print axioms routeBPaperFaithfulPiPhiHeadSpan_routeBNFrameGaugeSubgoals_of_zeroProfileQuotientedShiftCommonSpan
#print axioms routeBPaperFaithfulPiPhiHeadSpan_routeBNFrameGaugeSubgoals_of_retarget_zeroProfileQuotientedShiftCommonSpan
#print axioms cookLevinRichProjectionTarget_of_PiPhiHeadSpan_zeroProfileQuotientedShiftCommonSpan
#print axioms cookLevinRichProjectionTarget_of_PiPhiHeadSpan_retarget_zeroProfileQuotientedShiftCommonSpan

end PallLean.Paper93.Paper283
