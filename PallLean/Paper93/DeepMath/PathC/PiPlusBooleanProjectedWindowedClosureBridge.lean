import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedWindowedRankBridge
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeRealFrontier

/-!
# Windowed Route-C closure bridge for Boolean-projected Pi+

After the local obstruction, exact rank monotonicity at the same `(κ,ℓ)` window
is not the right intermediate target.  The honest statement is an inflated
window bound.  This file packages the corresponding P-side interface and shows
that it is still enough for the SAT-decider contradiction, because the final gap
only needs the gauged P-side bound and the projected NP lower bound.
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

/-- Windowed Route-B P-side input: the source compiled polynomial has bounded
inclusive SPDP rank at the enlarged Route-C window. -/
def RouteBSATWindowedIncPSideRankBound
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  mlBlockedSpdpRankInc
    (cook_levin_compilation M n hn2 htb hns).partition
    (Nat.log 2 n + extraK) (Nat.log 2 n + extraL)
    (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤ n ^ 200

/-- A windowed row certificate plus the matching enlarged P-side bound gives
the ordinary projected P-side bound for the Boolean-projected `Pi+` gauge. -/
theorem piPlusBooleanProjected_pSideBound_of_windowedRowCertificate_of_windowedIncPSide
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hrow : PiPlusBooleanProjectedWindowedRawPullbackRowCertificate
      extraK extraL M n hn2 htb hns piP)
    (hpside : RouteBSATWindowedIncPSideRankBound
      extraK extraL M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP) := by
  unfold SATDeciderGaugePSideBound RouteBSATWindowedIncPSideRankBound at *
  exact le_trans
    (piPlusBooleanProjected_rank_le_rankInc_of_windowedRowCertificate
      extraK extraL M n hn2 htb hns piP hrow
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)))
    hpside

/-- Paper-scale version of the windowed P-side bridge. -/
theorem cookLevinPiPlusBooleanProjected_pSideBound_paperScale_of_windowedRowCertificate_of_windowedIncPSide
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrow : PaperScalePiPlusBooleanProjectedWindowedRawPullbackRowCertificate
      extraK extraL M htb hns)
    (hpside : RouteBSATWindowedIncPSideRankBound
      extraK extraL M (2 ^ 804) paperScale_ge_two htb hns) :
    SATDeciderGaugePSideBound M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) :=
  piPlusBooleanProjected_pSideBound_of_windowedRowCertificate_of_windowedIncPSide
    extraK extraL M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hrow hpside

/-- Windowed Route-C closure data sufficient for the final contradiction.  This
is weaker and more honest than the old full-rank-monotone frontier: it asks only
for the windowed row certificate, the matching windowed P-side bound, and the
projected NP lower bound. -/
structure PaperScalePiPlusBooleanProjectedWindowedContradictionData
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  windowed_row_certificate :
    PaperScalePiPlusBooleanProjectedWindowedRawPullbackRowCertificate
      extraK extraL M htb hns
  windowed_p_side_bound :
    RouteBSATWindowedIncPSideRankBound
      extraK extraL M (2 ^ 804) paperScale_ge_two htb hns
  projected_np_lower_bound :
    RouteBSATProjectedNPIdentityMinorLowerBound M (2 ^ 804)
      paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns)

/-- Windowed Route-C closure data yields the ordinary P/NP incompatible pair
for the Boolean-projected `Pi+` gauge. -/
theorem pSide_and_npIdentityMinor_of_windowedContradictionData
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedWindowedContradictionData
      extraK extraL M htb hns) :
    SATDeciderGaugePSideBound M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) ∧
      SATDeciderGaugeNPIdentityMinorPreservation M (2 ^ 804)
        paperScale_ge_two htb hns
        (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) := by
  refine ⟨?_, ?_⟩
  · exact cookLevinPiPlusBooleanProjected_pSideBound_paperScale_of_windowedRowCertificate_of_windowedIncPSide
      extraK extraL M htb hns
      D.windowed_row_certificate D.windowed_p_side_bound
  · exact piPlusBooleanProjected_npIdentityMinorPreservation_of_projectedLowerBound
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusSATTransform_paperScale M htb hns)
      D.projected_np_lower_bound

/-- The corrected windowed Route-C data is already enough to rule out a bounded
SAT decider at paper scale.  Full same-window rank monotonicity is not needed
for this final contradiction once the windowed P-side bound is supplied. -/
theorem no_decidesSAT_at_paperScale_of_windowedContradictionData
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedWindowedContradictionData
      extraK extraL M htb hns) :
    ¬ DecidesSAT M := by
  intro hdec
  rcases pSide_and_npIdentityMinor_of_windowedContradictionData
    extraK extraL M htb hns D with ⟨hP, hNP⟩
  exact satDeciderGauge_pSide_and_npIdentityMinor_incompatible_at_large_n
    M (2 ^ 804) (le_rfl : 2 ^ 804 ≥ 2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns)
    hdec hP hNP

/-! ## Axiom audit anchors -/

#print axioms piPlusBooleanProjected_pSideBound_of_windowedRowCertificate_of_windowedIncPSide
#print axioms cookLevinPiPlusBooleanProjected_pSideBound_paperScale_of_windowedRowCertificate_of_windowedIncPSide
#print axioms pSide_and_npIdentityMinor_of_windowedContradictionData
#print axioms no_decidesSAT_at_paperScale_of_windowedContradictionData

end PallLean.Paper93.DeepMath.PathC
