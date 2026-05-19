import PallLean.Paper93.DeepMath.PathC.PiPlusOneOneFinalRoute

/-!
# One-one final frontier

Same-block rest factors force the P-side source window to `(1,1)`.  This file
adds the final contradiction-facing Route-C surface for that widened target.  It
keeps the corresponding Route-B `(1,1)` P-side rank bound explicit rather than
pretending the older `(1,0)` zero/common-span package supplies it.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- Paper-scale Route-B P-side rank bound at the widened `(1,1)` source window. -/
abbrev PaperScaleRouteBSATWindowedIncPSideRankBoundOneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  RouteBSATWindowedIncPSideRankBound 1 1
    M (2 ^ 804) paperScale_ge_two htb hns

/-- Paper-scale max-window Route-B P-side envelope at the widened `(1,1)` source
window. -/
abbrev PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  RouteBSATWindowedIncPSideRankEnvelope 1 1
    M (2 ^ 804) paperScale_ge_two htb hns

/-- The widened max-window envelope supplies the exact widened Route-B P-side
rank bound. -/
theorem paperScale_routeBSATWindowedIncPSideRankBoundOneOne_of_envelope
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns) :
    PaperScaleRouteBSATWindowedIncPSideRankBoundOneOne M htb hns :=
  routeBSATWindowedIncPSideRankBound_of_envelope
    1 1 M (2 ^ 804) paperScale_ge_two htb hns henv

/-- The widened P-side inclusion plus the matching Route-B widened P-side rank
bound gives the ordinary projected P-side field. -/
theorem paperScalePiPlusBooleanProjected_pSideBound_of_compiledPSubspaceInclusionOneOne_of_routeB
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hincl : PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneOne
      M htb hns)
    (hpside : PaperScaleRouteBSATWindowedIncPSideRankBoundOneOne M htb hns) :
    SATDeciderGaugePSideBound M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) :=
  piPlusBooleanProjected_pSideBound_of_compiledPSubspaceInclusion_of_windowedIncPSide
    1 1 M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hincl hpside

/-- The widened P-side inclusion, the matching Route-B `(1,1)` rank bound, and
NP-window subspace inclusion give the incompatible P/NP pair. -/
theorem pSide_and_npIdentityMinor_of_oneOneFinalInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hincl : PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneOne
      M htb hns)
    (hpside : PaperScaleRouteBSATWindowedIncPSideRankBoundOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    SATDeciderGaugePSideBound M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) ∧
      SATDeciderGaugeNPIdentityMinorPreservation M (2 ^ 804)
        paperScale_ge_two htb hns
        (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) := by
  refine ⟨?_, ?_⟩
  · exact paperScalePiPlusBooleanProjected_pSideBound_of_compiledPSubspaceInclusionOneOne_of_routeB
      M htb hns hincl hpside
  · exact piPlusBooleanProjected_npIdentityMinorPreservation_of_projectedLowerBound
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusSATTransform_paperScale M htb hns)
      (paperScale_routeBSATProjectedNPIdentityMinorLowerBound_of_npWindowRankNondecreasing
        M htb hns
        (paperScale_npWindowRankNondecreasing_of_npWindowSubspaceInclusion
          M htb hns hnp))

/-- Final widened Route-C frontier data. -/
structure PaperScalePiPlusBooleanProjectedOneOneFinalFrontierData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) where
  compiled_p_subspace_inclusion :
    PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneOne M htb hns
  routeB_windowed_p_side_bound :
    PaperScaleRouteBSATWindowedIncPSideRankBoundOneOne M htb hns
  np_subspace_inclusion :
    PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns

/-- Final widened frontier data gives the incompatible P/NP pair. -/
theorem pSide_and_npIdentityMinor_of_oneOneFinalFrontierData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedOneOneFinalFrontierData M htb hns) :
    SATDeciderGaugePSideBound M (2 ^ 804) paperScale_ge_two htb hns
        (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) ∧
      SATDeciderGaugeNPIdentityMinorPreservation M (2 ^ 804)
        paperScale_ge_two htb hns
        (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) :=
  pSide_and_npIdentityMinor_of_oneOneFinalInputs
    M htb hns D.compiled_p_subspace_inclusion
    D.routeB_windowed_p_side_bound D.np_subspace_inclusion

/-- Final widened Route-C/Route-B frontier theorem. -/
theorem no_decidesSAT_at_paperScale_of_oneOneFinalFrontierData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedOneOneFinalFrontierData M htb hns) :
    ¬ DecidesSAT M := by
  intro hdec
  rcases pSide_and_npIdentityMinor_of_oneOneFinalFrontierData M htb hns D with ⟨hP, hNP⟩
  exact satDeciderGauge_pSide_and_npIdentityMinor_incompatible_at_large_n
    M (2 ^ 804) (le_rfl : 2 ^ 804 ≥ 2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns)
    hdec hP hNP

/-- P-side closeout inputs plus the explicit non-P-side final inputs give the
widened final frontier data. -/
def paperScale_oneOneFinalFrontierData_of_psideCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOnePsideCloseoutInputs
      M htb hns)
    (hpside : PaperScaleRouteBSATWindowedIncPSideRankBoundOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    PaperScalePiPlusBooleanProjectedOneOneFinalFrontierData M htb hns where
  compiled_p_subspace_inclusion :=
    paperScale_compiledPSubspaceInclusionOneOne_of_psideCloseoutInputs
      M htb hns hinputs
  routeB_windowed_p_side_bound := hpside
  np_subspace_inclusion := hnp

/-- P-side closeout inputs plus explicit Route-B `(1,1)` and NP-side inputs rule
out a SAT decider at paper scale. -/
theorem no_decidesSAT_at_paperScale_of_oneOnePsideCloseoutInputs_routeB_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOnePsideCloseoutInputs
      M htb hns)
    (hpside : PaperScaleRouteBSATWindowedIncPSideRankBoundOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_oneOneFinalFrontierData
    M htb hns
    (paperScale_oneOneFinalFrontierData_of_psideCloseoutInputs
      M htb hns hinputs hpside hnp)

/-- P-side closeout inputs plus a Route-B `(1,1)` envelope and NP-side input rule
out a SAT decider at paper scale. -/
theorem no_decidesSAT_at_paperScale_of_oneOnePsideCloseoutInputs_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOnePsideCloseoutInputs
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_oneOnePsideCloseoutInputs_routeB_npInclusion
    M htb hns hinputs
    (paperScale_routeBSATWindowedIncPSideRankBoundOneOne_of_envelope
      M htb hns henv)
    hnp

/-- Polynomial span plus local-factor-to-allocation reduction plus explicit
Route-B `(1,1)` and NP-side inputs rule out a SAT decider at paper scale. -/
theorem no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorReduction_routeB_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns)
    (hpside : PaperScaleRouteBSATWindowedIncPSideRankBoundOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_oneOnePsideCloseoutInputs_routeB_npInclusion
    M htb hns
    { polynomial_span := hpoly, local_factor_to_allocation := hred }
    hpside hnp

/-- Polynomial span plus local-factor-to-allocation reduction plus a Route-B
`(1,1)` envelope and NP-side input rule out a SAT decider at paper scale. -/
theorem no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpoly : PaperScalePiPlusBooleanProjectedNormalizedDerivativePolynomialSpan
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorReduction_routeB_npInclusion
    M htb hns hpoly hred
    (paperScale_routeBSATWindowedIncPSideRankBoundOneOne_of_envelope
      M htb hns henv)
    hnp

/-! ## Axiom audit anchors -/

#print axioms paperScale_routeBSATWindowedIncPSideRankBoundOneOne_of_envelope
#print axioms paperScalePiPlusBooleanProjected_pSideBound_of_compiledPSubspaceInclusionOneOne_of_routeB
#print axioms pSide_and_npIdentityMinor_of_oneOneFinalInputs
#print axioms pSide_and_npIdentityMinor_of_oneOneFinalFrontierData
#print axioms no_decidesSAT_at_paperScale_of_oneOneFinalFrontierData
#print axioms paperScale_oneOneFinalFrontierData_of_psideCloseoutInputs
#print axioms no_decidesSAT_at_paperScale_of_oneOnePsideCloseoutInputs_routeB_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_oneOnePsideCloseoutInputs_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorReduction_routeB_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorReduction_routeBEnvelope_npInclusion

end PallLean.Paper93.DeepMath.PathC
