import PallLean.Paper93.DeepMath.PathC.PiPlusOneOneNormalizedCriterionCloseout

/-!
# Split normalized-derivative criterion

The normalized-derivative criterion has two independent algebraic pieces:

1. derivative/Boolean-normalization commutation for the transformed local-factor
   product; and
2. Boolean-normalization stability of the distributed Leibniz generator span.

This file separates those obligations and wires the split surface into the
widened `(1,1)` final route.  No product theorem is asserted here; the split
just gives the next algebraic targets precise names.
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

/-- Commutation half of the normalized-derivative criterion: after forming the
Boolean-projected transformed local-factor list `L`, differentiating the Boolean
normal representative of `L.prod` agrees with Boolean-normalizing the raw
derivative row. -/
def PiPlusBooleanProjectedNormalizedDerivativeCommutation
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
    S.length = Nat.log 2 n →
    isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      let L := piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D
      iterDerivList S (zeroProfileBooleanNormalize L.prod) =
        zeroProfileBooleanNormalize (iterDerivList S L.prod)

/-- Stability half of the normalized-derivative criterion: Boolean-normalizing a
distributed Leibniz generator stays in the span of the same distributed
generator set. -/
def PiPlusBooleanProjectedDistributedGeneratorBooleanStability
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
    S.length = Nat.log 2 n →
    isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      let L := piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D
      let G := distribDerivProds Finset.univ
        (fun i : Fin L.length => L[i.val]) S
      ∀ q ∈ G, zeroProfileBooleanNormalize q ∈ Submodule.span ℚ G

/-- The split commutation/stability obligations reassemble into the existing
normalized-derivative criterion. -/
theorem normalizedDerivativeCriterion_of_commutation_and_stability
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hcomm : PiPlusBooleanProjectedNormalizedDerivativeCommutation
      M n hn2 htb hns D)
    (hstable : PiPlusBooleanProjectedDistributedGeneratorBooleanStability
      M n hn2 htb hns D) :
    PiPlusBooleanProjectedNormalizedDerivativeCriterion M n hn2 htb hns D := by
  intro S hSlen hadm
  constructor
  · exact hcomm S hSlen hadm
  · exact hstable S hSlen hadm

/-- Paper-scale commutation obligation. -/
abbrev PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedNormalizedDerivativeCommutation
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale distributed-generator Boolean-stability obligation. -/
abbrev PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStability
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedDistributedGeneratorBooleanStability
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale normalized-derivative criterion from the split obligations. -/
theorem paperScale_normalizedDerivativeCriterion_of_commutation_and_stability
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hstable : PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStability
      M htb hns) :
    PaperScalePiPlusBooleanProjectedNormalizedDerivativeCriterion M htb hns :=
  normalizedDerivativeCriterion_of_commutation_and_stability
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    hcomm hstable

/-- Split normalized-criterion obligations plus local-factor-to-allocation
reduction close the `(1,1)` factored row-span classifier. -/
theorem paperScale_factoredRowSpanClassifierOneOne_of_normalizedCriterionSplit_and_localFactorReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hstable : PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStability
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedFactoredRowSpanClassifierOneOne M htb hns :=
  paperScale_factoredRowSpanClassifierOneOne_of_normalizedCriterion_and_localFactorReduction
    M htb hns
    (paperScale_normalizedDerivativeCriterion_of_commutation_and_stability
      M htb hns hcomm hstable)
    hred

/-- Split normalized-criterion obligations plus local-factor-to-allocation
reduction close the `(1,1)` compiled P-subspace inclusion. -/
theorem paperScale_compiledPSubspaceInclusionOneOne_of_normalizedCriterionSplit_and_localFactorReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hstable : PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStability
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneOne M htb hns :=
  paperScale_compiledPSubspaceInclusionOneOne_of_normalizedCriterion_and_localFactorReduction
    M htb hns
    (paperScale_normalizedDerivativeCriterion_of_commutation_and_stability
      M htb hns hcomm hstable)
    hred

/-- Final envelope closeout from the split normalized-criterion obligations. -/
theorem no_decidesSAT_at_paperScale_of_normalizedCriterionSplit_localFactorReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hstable : PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStability
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_normalizedCriterion_localFactorReduction_routeBEnvelope_npInclusion
    M htb hns
    (paperScale_normalizedDerivativeCriterion_of_commutation_and_stability
      M htb hns hcomm hstable)
    hred henv hnp

/-- Compact final input package using the split normalized-criterion obligations. -/
structure PaperScalePiPlusBooleanProjectedOneOneSplitCriterionCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  commutation : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
    M htb hns
  stability : PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStability
    M htb hns
  local_factor_to_allocation :
    PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns
  routeB_envelope : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns
  np_subspace_inclusion : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion
    M htb hns

/-- The compact split-criterion input package rules out a SAT decider. -/
theorem no_decidesSAT_at_paperScale_of_oneOneSplitCriterionCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOneSplitCriterionCloseoutInputs
      M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_normalizedCriterionSplit_localFactorReduction_routeBEnvelope_npInclusion
    M htb hns hinputs.commutation hinputs.stability
    hinputs.local_factor_to_allocation hinputs.routeB_envelope
    hinputs.np_subspace_inclusion

/-! ## Axiom audit anchors -/

#print axioms normalizedDerivativeCriterion_of_commutation_and_stability
#print axioms paperScale_normalizedDerivativeCriterion_of_commutation_and_stability
#print axioms paperScale_factoredRowSpanClassifierOneOne_of_normalizedCriterionSplit_and_localFactorReduction
#print axioms paperScale_compiledPSubspaceInclusionOneOne_of_normalizedCriterionSplit_and_localFactorReduction
#print axioms no_decidesSAT_at_paperScale_of_normalizedCriterionSplit_localFactorReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_oneOneSplitCriterionCloseoutInputs

end PallLean.Paper93.DeepMath.PathC
