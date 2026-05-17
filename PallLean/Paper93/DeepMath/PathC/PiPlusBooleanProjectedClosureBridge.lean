import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedTransportBridge
import PallLean.Paper93.Paper283.RouteBTransportPSideBound
import PallLean.Paper93.Paper283.RouteBMatrixToSATGauge

/-!
# Closing bridges for Boolean-projected Route C

The rank part of corrected Route C is now reduced to raw-pullback membership.
This file wires that rank criterion to the remaining SAT-gauge fields:

* the projected P-side bound follows from rank monotonicity plus the unprojected
  Route-B/Cook--Levin P-side bound;
* the NP identity-minor field follows from the corresponding projected lower
  bound used in the Route-B transport vocabulary;
* together these package the full Boolean-projected Route-C frontier.

This does not claim the analytic/profile blockers are already proved; it makes
exactly clear which Route-B outputs feed the constructive `Pi+ᵦ` candidate.
-/

namespace PallLean.Paper93.DeepMath.PathC

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000
set_option linter.unnecessarySimpa false

/-- Rank monotonicity plus the unprojected Cook--Levin P-side estimate gives the
P-side field for the Boolean-projected `Pi+` gauge. -/
theorem piPlusBooleanProjected_pSideBound_of_rawPullbackGeneratorMembership_of_unprojectedPSide
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hpull : PiPlusBooleanProjectedRawPullbackGeneratorMembership
      M n hn2 htb hns piP)
    (hpside : RouteBSATUnprojectedPSideRankBound M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP) := by
  have hrank : SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP) :=
    piPlusBooleanProjected_rankMonotonicity_of_backwardGeneratorTransport
      M n hn2 htb hns piP
      (piPlusBooleanProjectedBackwardGeneratorTransport_of_rawPullbackGeneratorMembership
        M n hn2 htb hns piP hpull)
  exact le_trans
    (hrank (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
    hpside

/-- Paper-scale specialization of the P-side bridge. -/
theorem cookLevinPiPlusBooleanProjected_pSideBound_paperScale_of_rawPullbackGeneratorMembership_of_unprojectedPSide
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpull : PaperScalePiPlusBooleanProjectedRawPullbackGeneratorMembership
      M htb hns)
    (hpside : RouteBSATUnprojectedPSideRankBound M (2 ^ 804)
      paperScale_ge_two htb hns) :
    SATDeciderGaugePSideBound M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) :=
  piPlusBooleanProjected_pSideBound_of_rawPullbackGeneratorMembership_of_unprojectedPSide
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hpull hpside

/-- The Route-B projected NP lower-bound vocabulary is exactly the SAT-gauge
identity-minor preservation field, after adding the `DecidesSAT` argument. -/
theorem piPlusBooleanProjected_npIdentityMinorPreservation_of_projectedLowerBound
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hlower : RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP)) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP) := by
  intro _hdec
  exact hlower

/-- Paper-scale specialization of the NP identity-minor bridge. -/
theorem cookLevinPiPlusBooleanProjected_npIdentityMinorPreservation_paperScale_of_projectedLowerBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hlower : RouteBSATProjectedNPIdentityMinorLowerBound M (2 ^ 804)
      paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns)) :
    SATDeciderGaugeNPIdentityMinorPreservation M (2 ^ 804)
      paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) :=
  piPlusBooleanProjected_npIdentityMinorPreservation_of_projectedLowerBound
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hlower

/-- Raw-pullback membership plus the two Route-B rank outputs package the full
corrected Boolean-projected Route-C frontier. -/
theorem piPlusBooleanProjected_frontier_of_rawPullback_unprojectedPSide_projectedNP
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hpull : PiPlusBooleanProjectedRawPullbackGeneratorMembership
      M n hn2 htb hns piP)
    (hpside : RouteBSATUnprojectedPSideRankBound M n hn2 htb hns)
    (hlower : RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP)) :
    PiPlusBooleanProjectedSATGaugeFrontier M n hn2 htb hns piP where
  backward_generator_transport :=
    piPlusBooleanProjectedBackwardGeneratorTransport_of_rawPullbackGeneratorMembership
      M n hn2 htb hns piP hpull
  p_side_bound :=
    piPlusBooleanProjected_pSideBound_of_rawPullbackGeneratorMembership_of_unprojectedPSide
      M n hn2 htb hns piP hpull hpside
  identity_minor_preservation :=
    piPlusBooleanProjected_npIdentityMinorPreservation_of_projectedLowerBound
      M n hn2 htb hns piP hlower

/-- Paper-scale package theorem for the corrected Route-C frontier. -/
theorem paperScalePiPlusBooleanProjected_frontier_of_rawPullback_unprojectedPSide_projectedNP
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpull : PaperScalePiPlusBooleanProjectedRawPullbackGeneratorMembership
      M htb hns)
    (hpside : RouteBSATUnprojectedPSideRankBound M (2 ^ 804)
      paperScale_ge_two htb hns)
    (hlower : RouteBSATProjectedNPIdentityMinorLowerBound M (2 ^ 804)
      paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns)) :
    PaperScalePiPlusBooleanProjectedSATGaugeFrontier M htb hns :=
  piPlusBooleanProjected_frontier_of_rawPullback_unprojectedPSide_projectedNP
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)
    hpull hpside hlower

/-- A tiny arithmetic helper for using active-template Route-B blockers at exact
paper scale. -/
theorem paperScale_two_pow_804_ge_four : (2 : Nat) ^ 804 ≥ 4 := by
  have hbase : 1 ≤ (2 : Nat) := by norm_num
  have hexp : 2 ≤ 804 := by norm_num
  have hpow : (2 : Nat) ^ 2 ≤ (2 : Nat) ^ 804 :=
    Nat.pow_le_pow_right hbase hexp
  simpa using hpow

/-- If the current Route-B active-template blockers are supplied, they provide
the unprojected P-side input for the corrected Route-C frontier. -/
theorem paperScalePiPlusBooleanProjected_frontier_of_rawPullback_activeTemplateBlockers_projectedNP
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpull : PaperScalePiPlusBooleanProjectedRawPullbackGeneratorMembership
      M htb hns)
    (hblock : CookLevinActiveProfileTemplateCollapseBlockers M (2 ^ 804)
      paperScale_ge_two htb hns)
    (hlower : RouteBSATProjectedNPIdentityMinorLowerBound M (2 ^ 804)
      paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns)) :
    PaperScalePiPlusBooleanProjectedSATGaugeFrontier M htb hns :=
  paperScalePiPlusBooleanProjected_frontier_of_rawPullback_unprojectedPSide_projectedNP
    M htb hns hpull
    (routeBSATUnprojectedPSideRankBound_of_activeTemplateBlockers
      M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four
      hblock)
    hlower

/-! ## Axiom audit anchors -/

#print axioms piPlusBooleanProjected_pSideBound_of_rawPullbackGeneratorMembership_of_unprojectedPSide
#print axioms cookLevinPiPlusBooleanProjected_pSideBound_paperScale_of_rawPullbackGeneratorMembership_of_unprojectedPSide
#print axioms piPlusBooleanProjected_npIdentityMinorPreservation_of_projectedLowerBound
#print axioms piPlusBooleanProjected_frontier_of_rawPullback_unprojectedPSide_projectedNP
#print axioms paperScalePiPlusBooleanProjected_frontier_of_rawPullback_unprojectedPSide_projectedNP
#print axioms paperScale_two_pow_804_ge_four
#print axioms paperScalePiPlusBooleanProjected_frontier_of_rawPullback_activeTemplateBlockers_projectedNP

end PallLean.Paper93.DeepMath.PathC
