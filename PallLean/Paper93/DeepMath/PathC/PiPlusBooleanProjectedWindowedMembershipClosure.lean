import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedWindowedClosureBridge

/-!
# Windowed membership closure for Boolean-projected Pi+

The row-certificate interface is deliberately strong: it asks for every pulled
back target generator to be represented by one explicit enlarged source row.
For the rank argument, however, we only need membership in the enlarged
inclusive source SPDP subspace.  This file packages that weaker and more
realistic Route-C closure surface.

This does not discard the row-certificate route: row certificates still imply
membership via `piPlusBooleanProjectedWindowedRawPullbackGeneratorMembership_of_windowedRowCertificate`.
It simply exposes the actual theorem socket used by the rank proof.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- Paper-scale windowed raw-pullback membership abbreviation. -/
abbrev PaperScalePiPlusBooleanProjectedWindowedRawPullbackMembership
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedWindowedRawPullbackGeneratorMembership extraK extraL
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Windowed pullback membership plus the matching enlarged Route-B P-side bound
gives the ordinary projected P-side bound for the Boolean-projected `Pi+` gauge. -/
theorem piPlusBooleanProjected_pSideBound_of_windowedMembership_of_windowedIncPSide
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hpull : PiPlusBooleanProjectedWindowedRawPullbackGeneratorMembership
      extraK extraL M n hn2 htb hns piP)
    (hpside : RouteBSATWindowedIncPSideRankBound
      extraK extraL M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP) := by
  unfold SATDeciderGaugePSideBound RouteBSATWindowedIncPSideRankBound at *
  exact le_trans
    (piPlusBooleanProjected_rank_le_rankInc_of_windowedRawPullbackMembership
      extraK extraL M n hn2 htb hns piP hpull
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
    hpside

/-- Paper-scale version of the membership P-side bridge. -/
theorem cookLevinPiPlusBooleanProjected_pSideBound_paperScale_of_windowedMembership_of_windowedIncPSide
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpull : PaperScalePiPlusBooleanProjectedWindowedRawPullbackMembership
      extraK extraL M htb hns)
    (hpside : RouteBSATWindowedIncPSideRankBound
      extraK extraL M (2 ^ 804) paperScale_ge_two htb hns) :
    SATDeciderGaugePSideBound M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) :=
  piPlusBooleanProjected_pSideBound_of_windowedMembership_of_windowedIncPSide
    extraK extraL M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hpull hpside

/-- Weaker/more direct windowed Route-C contradiction data: membership rather
than explicit row equality. -/
structure PaperScalePiPlusBooleanProjectedWindowedMembershipContradictionData
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  windowed_pullback_membership :
    PaperScalePiPlusBooleanProjectedWindowedRawPullbackMembership
      extraK extraL M htb hns
  windowed_p_side_bound :
    RouteBSATWindowedIncPSideRankBound
      extraK extraL M (2 ^ 804) paperScale_ge_two htb hns
  projected_np_lower_bound :
    RouteBSATProjectedNPIdentityMinorLowerBound M (2 ^ 804)
      paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns)

/-- Row-certificate data canonically gives the weaker membership data. -/
theorem membershipContradictionData_of_rowContradictionData
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedWindowedContradictionData
      extraK extraL M htb hns) :
    PaperScalePiPlusBooleanProjectedWindowedMembershipContradictionData
      extraK extraL M htb hns where
  windowed_pullback_membership :=
    piPlusBooleanProjectedWindowedRawPullbackGeneratorMembership_of_windowedRowCertificate
      extraK extraL M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusSATTransform_paperScale M htb hns)
      D.windowed_row_certificate
  windowed_p_side_bound := D.windowed_p_side_bound
  projected_np_lower_bound := D.projected_np_lower_bound

/-- Membership-based Route-C closure data yields the ordinary incompatible P/NP
pair for the Boolean-projected `Pi+` gauge. -/
theorem pSide_and_npIdentityMinor_of_windowedMembershipContradictionData
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedWindowedMembershipContradictionData
      extraK extraL M htb hns) :
    SATDeciderGaugePSideBound M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) ∧
      SATDeciderGaugeNPIdentityMinorPreservation M (2 ^ 804)
        paperScale_ge_two htb hns
        (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) := by
  refine ⟨?_, ?_⟩
  · exact cookLevinPiPlusBooleanProjected_pSideBound_paperScale_of_windowedMembership_of_windowedIncPSide
      extraK extraL M htb hns
      D.windowed_pullback_membership D.windowed_p_side_bound
  · exact piPlusBooleanProjected_npIdentityMinorPreservation_of_projectedLowerBound
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusSATTransform_paperScale M htb hns)
      D.projected_np_lower_bound

/-- Membership-level Route-C data is enough to rule out a bounded SAT decider
at paper scale. -/
theorem no_decidesSAT_at_paperScale_of_windowedMembershipContradictionData
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedWindowedMembershipContradictionData
      extraK extraL M htb hns) :
    ¬ DecidesSAT M := by
  intro hdec
  rcases pSide_and_npIdentityMinor_of_windowedMembershipContradictionData
    extraK extraL M htb hns D with ⟨hP, hNP⟩
  exact satDeciderGauge_pSide_and_npIdentityMinor_incompatible_at_large_n
    M (2 ^ 804) (le_rfl : 2 ^ 804 ≥ 2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns)
    hdec hP hNP

/-- One-window specialization of the membership-level final data. -/
abbrev PaperScalePiPlusBooleanProjectedOneWindowMembershipContradictionData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PaperScalePiPlusBooleanProjectedWindowedMembershipContradictionData 1 0 M htb hns

/-- One-window membership-level final closure theorem. -/
theorem no_decidesSAT_at_paperScale_of_oneWindowMembershipContradictionData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedOneWindowMembershipContradictionData
      M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_windowedMembershipContradictionData
    1 0 M htb hns D

/-! ## Axiom audit anchors -/

#print axioms piPlusBooleanProjected_pSideBound_of_windowedMembership_of_windowedIncPSide
#print axioms cookLevinPiPlusBooleanProjected_pSideBound_paperScale_of_windowedMembership_of_windowedIncPSide
#print axioms membershipContradictionData_of_rowContradictionData
#print axioms pSide_and_npIdentityMinor_of_windowedMembershipContradictionData
#print axioms no_decidesSAT_at_paperScale_of_windowedMembershipContradictionData
#print axioms no_decidesSAT_at_paperScale_of_oneWindowMembershipContradictionData

end PallLean.Paper93.DeepMath.PathC
