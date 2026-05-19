import PallLean.Paper93.DeepMath.PathC.PiPlusOneOneFinalFrontier
import PallLean.Paper93.DeepMath.PathC.PiPlusNormalizedDerivativeCriterion

/-!
# One-one closeout from the normalized-derivative criterion

The widened `(1,1)` final frontier currently consumes the polynomial-level
normalized derivative span.  The older normalized-derivative criterion is a more
local algebra target: derivative/Boolean-normalization commutation plus
normalization stability of distributed Leibniz generators.

This file wires that criterion directly into the `(1,1)` route, so the remaining
P-side work can target the criterion rather than the broader polynomial-span
payload.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open LeibnizProduct

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- The normalized-derivative criterion plus local-factor-to-allocation reduction
closes the `(1,1)` factored row-span classifier. -/
theorem paperScale_factoredRowSpanClassifierOneOne_of_normalizedCriterion_and_localFactorReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcrit : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCriterion M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne M htb hns :=
  paperScale_factoredRowSpanClassifierOneOne_of_polynomialSpan_and_localFactorReduction
    M htb hns
    (paperScale_normalizedDerivativePolynomialSpan_of_criterion M htb hns hcrit)
    hred

/-- The normalized-derivative criterion plus local-factor-to-allocation reduction
closes the `(1,1)` compiled raw-pullback socket. -/
theorem paperScale_windowedCompiledRawPullbackMembershipOneOne_of_normalizedCriterion_and_localFactorReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcrit : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCriterion M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedWindowedCompiledRawPullbackMembershipOneOne
      M htb hns :=
  paperScale_windowedCompiledRawPullbackMembershipOneOne_of_rowSpanClassifier
    M htb hns
    (paperScale_factoredRowSpanClassifierOneOne_of_normalizedCriterion_and_localFactorReduction
      M htb hns hcrit hred)

/-- The normalized-derivative criterion plus local-factor-to-allocation reduction
closes the `(1,1)` compiled P-subspace inclusion socket. -/
theorem paperScale_compiledPSubspaceInclusionOneOne_of_normalizedCriterion_and_localFactorReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcrit : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCriterion M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneOne
      M htb hns :=
  paperScale_compiledPSubspaceInclusionOneOne_of_rowSpanClassifier
    M htb hns
    (paperScale_factoredRowSpanClassifierOneOne_of_normalizedCriterion_and_localFactorReduction
      M htb hns hcrit hred)

/-- The normalized-derivative criterion plus local-factor-to-allocation reduction
and explicit final non-P-side inputs rule out a SAT decider. -/
theorem no_decidesSAT_at_paperScale_of_normalizedCriterion_localFactorReduction_routeB_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcrit : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCriterion M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns)
    (hpside : PaperScaleRouteBSATWindowedIncPSideRankBoundOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_polynomialSpan_localFactorReduction_routeB_npInclusion
    M htb hns
    (paperScale_normalizedDerivativePolynomialSpan_of_criterion M htb hns hcrit)
    hred hpside hnp

/-- Envelope variant of the normalized-criterion closeout. -/
theorem no_decidesSAT_at_paperScale_of_normalizedCriterion_localFactorReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcrit : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCriterion M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_normalizedCriterion_localFactorReduction_routeB_npInclusion
    M htb hns hcrit hred
    (paperScale_routeBSATWindowedIncPSideRankBoundOneOne_of_envelope
      M htb hns henv)
    hnp

/-- Compact final input package using the local normalized-derivative criterion
rather than the broader polynomial-span theorem. -/
structure PaperScalePiPlusBooleanProjectedOneOneCriterionCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  normalized_criterion : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCriterion
    M htb hns
  local_factor_to_allocation :
    PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns
  routeB_envelope : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns
  np_subspace_inclusion : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion
    M htb hns

/-- The compact normalized-criterion input package rules out a SAT decider. -/
theorem no_decidesSAT_at_paperScale_of_oneOneCriterionCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOneCriterionCloseoutInputs
      M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_normalizedCriterion_localFactorReduction_routeBEnvelope_npInclusion
    M htb hns hinputs.normalized_criterion
    hinputs.local_factor_to_allocation hinputs.routeB_envelope
    hinputs.np_subspace_inclusion

/-! ## Axiom audit anchors -/

#print axioms paperScale_factoredRowSpanClassifierOneOne_of_normalizedCriterion_and_localFactorReduction
#print axioms paperScale_windowedCompiledRawPullbackMembershipOneOne_of_normalizedCriterion_and_localFactorReduction
#print axioms paperScale_compiledPSubspaceInclusionOneOne_of_normalizedCriterion_and_localFactorReduction
#print axioms no_decidesSAT_at_paperScale_of_normalizedCriterion_localFactorReduction_routeB_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_normalizedCriterion_localFactorReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_oneOneCriterionCloseoutInputs

end PallLean.Paper93.DeepMath.PathC
