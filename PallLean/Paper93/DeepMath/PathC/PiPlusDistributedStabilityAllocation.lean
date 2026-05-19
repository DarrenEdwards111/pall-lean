import PallLean.Paper93.DeepMath.PathC.PiPlusNormalizedCriterionSplit

/-!
# Allocation-level Boolean stability for distributed Leibniz generators

`distribDerivProds` packages each generator behind existential membership.  This
file opens that wrapper for the Boolean-stability half of the normalized
criterion: it is enough to prove stability for every concrete derivative
allocation function.
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

/-- Allocation-level Boolean stability for distributed Leibniz generators.  For
every concrete allocation of derivative sublists to transformed local factors,
the Boolean-normalized allocated product lies in the span of the whole
distributed-generator set. -/
def PiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
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
      ∀ (alloc : Fin L.length → List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
        (∀ i, ∀ v ∈ alloc i, v ∈ S) →
          zeroProfileBooleanNormalize
            (Finset.univ.prod (fun i : Fin L.length =>
              iterDerivList (alloc i) L[i.val])) ∈ Submodule.span ℚ G

/-- Allocation-level stability implies the original existential-set stability
surface by unpacking `q ∈ distribDerivProds`. -/
theorem distributedGeneratorBooleanStability_of_allocationStability
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (halloc : PiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
      M n hn2 htb hns D) :
    PiPlusBooleanProjectedDistributedGeneratorBooleanStability
      M n hn2 htb hns D := by
  intro S hSlen hadm
  change ∀ q ∈ distribDerivProds Finset.univ
      (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).length =>
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D)[i.val]) S,
      zeroProfileBooleanNormalize q ∈
        Submodule.span ℚ
          (distribDerivProds Finset.univ
            (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
                M n hn2 htb hns D).length =>
              (piPlusBooleanProjectedTransformedConstraintFactors
                M n hn2 htb hns D)[i.val]) S)
  intro q hq
  rcases hq with ⟨alloc, halloc_mem, rfl⟩
  exact halloc S hSlen hadm alloc halloc_mem

/-- Paper-scale allocation-level Boolean stability. -/
abbrev PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale set-level Boolean stability from allocation-level stability. -/
theorem paperScale_distributedGeneratorBooleanStability_of_allocationStability
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (halloc : PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
      M htb hns) :
    PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStability M htb hns :=
  distributedGeneratorBooleanStability_of_allocationStability
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) halloc

/-- Commutation plus allocation-level stability reassemble into the normalized
criterion. -/
theorem paperScale_normalizedDerivativeCriterion_of_commutation_and_allocationStability
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (halloc : PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
      M htb hns) :
    PaperScalePiPlusBooleanProjectedNormalizedDerivativeCriterion M htb hns :=
  paperScale_normalizedDerivativeCriterion_of_commutation_and_stability
    M htb hns hcomm
    (paperScale_distributedGeneratorBooleanStability_of_allocationStability
      M htb hns halloc)

/-- Commutation plus allocation-level stability and local-factor-to-allocation
reduction close the widened `(1,1)` compiled P-subspace inclusion. -/
theorem paperScale_compiledPSubspaceInclusionOneOne_of_commutation_allocationStability_localFactorReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hstableAlloc : PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedCompiledPSubspaceInclusionOneOne M htb hns :=
  paperScale_compiledPSubspaceInclusionOneOne_of_normalizedCriterion_and_localFactorReduction
    M htb hns
    (paperScale_normalizedDerivativeCriterion_of_commutation_and_allocationStability
      M htb hns hcomm hstableAlloc)
    hred

/-- Final envelope closeout from commutation, allocation-level stability, and the
local-factor-to-allocation reduction. -/
theorem no_decidesSAT_at_paperScale_of_commutation_allocationStability_localFactorReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hstableAlloc : PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_normalizedCriterion_localFactorReduction_routeBEnvelope_npInclusion
    M htb hns
    (paperScale_normalizedDerivativeCriterion_of_commutation_and_allocationStability
      M htb hns hcomm hstableAlloc)
    hred henv hnp

/-- Compact closeout package with allocation-level stability as the remaining
Boolean-stability target. -/
structure PaperScalePiPlusBooleanProjectedOneOneAllocationStabilityCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  commutation : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
    M htb hns
  allocation_stability :
    PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
      M htb hns
  local_factor_to_allocation :
    PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns
  routeB_envelope : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns
  np_subspace_inclusion : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion
    M htb hns

/-- The compact allocation-stability input package rules out a SAT decider. -/
theorem no_decidesSAT_at_paperScale_of_oneOneAllocationStabilityCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOneAllocationStabilityCloseoutInputs
      M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_allocationStability_localFactorReduction_routeBEnvelope_npInclusion
    M htb hns hinputs.commutation hinputs.allocation_stability
    hinputs.local_factor_to_allocation hinputs.routeB_envelope
    hinputs.np_subspace_inclusion

/-! ## Axiom audit anchors -/

#print axioms distributedGeneratorBooleanStability_of_allocationStability
#print axioms paperScale_distributedGeneratorBooleanStability_of_allocationStability
#print axioms paperScale_normalizedDerivativeCriterion_of_commutation_and_allocationStability
#print axioms paperScale_compiledPSubspaceInclusionOneOne_of_commutation_allocationStability_localFactorReduction
#print axioms no_decidesSAT_at_paperScale_of_commutation_allocationStability_localFactorReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_oneOneAllocationStabilityCloseoutInputs

end PallLean.Paper93.DeepMath.PathC
