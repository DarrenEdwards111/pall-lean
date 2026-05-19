import PallLean.Paper93.DeepMath.PathC.PiPlusDistributedStabilityAllocation

/-!
# Factor/product reduction for allocation-level Boolean stability

The previous allocation split replaced the opaque `q ∈ distribDerivProds` surface
by a concrete derivative-allocation product.  This file makes the next seam
smaller: allocation-level Boolean stability follows if Boolean-normalizing any
allocated product lands on another concrete distributed Leibniz generator.

This isolates the remaining algebraic content from the span bookkeeping.  The
hard part is now the product/factor theorem that constructs the normalized
allocation; the span closeout is immediate from `Submodule.subset_span`.
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

/-- Concrete allocated Leibniz product for transformed local factors. -/
noncomputable def piPlusBooleanProjectedAllocatedDerivativeProduct
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ :=
  let L := piPlusBooleanProjectedTransformedConstraintFactors M n hn2 htb hns D
  Finset.univ.prod (fun i : Fin L.length => iterDerivList (alloc i) L[i.val])

/-- Product/factor normalization target for one concrete allocation.

It says that Boolean-normalizing the allocated product is itself another
allocated product whose derivative sublists are still drawn from the ambient
Leibniz derivative list `S`. -/
def PiPlusBooleanProjectedAllocatedProductNormalizesToDistributedGenerator
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) : Prop :=
  ∃ alloc' : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars),
    (∀ i, ∀ v ∈ alloc' i, v ∈ S) ∧
      zeroProfileBooleanNormalize
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) =
        piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc'

/-- The remaining product/factor reduction for allocation-level stability: every
admissible concrete allocation normalizes to another distributed generator. -/
def PiPlusBooleanProjectedAllocationProductNormalizationReduction
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
    S.length = Nat.log 2 n →
    isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      ∀ (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).length →
        List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
        (∀ i, ∀ v ∈ alloc i, v ∈ S) →
          PiPlusBooleanProjectedAllocatedProductNormalizesToDistributedGenerator
            M n hn2 htb hns D S alloc

/-- If an allocated product normalizes to another distributed generator, its
Boolean normalization lies in the span of `distribDerivProds`. -/
theorem allocatedProduct_mem_span_of_normalizesToDistributedGenerator
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (hnorm : PiPlusBooleanProjectedAllocatedProductNormalizesToDistributedGenerator
      M n hn2 htb hns D S alloc) :
    zeroProfileBooleanNormalize
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc) ∈
      Submodule.span ℚ
        (distribDerivProds Finset.univ
          (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D).length =>
            (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D)[i.val]) S) := by
  rcases hnorm with ⟨alloc', halloc', hnorm_eq⟩
  rw [hnorm_eq]
  apply Submodule.subset_span
  refine ⟨alloc', halloc', ?_⟩
  rfl

/-- Product-normalization reduction implies allocation-level Boolean stability. -/
theorem allocationStability_of_productNormalizationReduction
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (hred : PiPlusBooleanProjectedAllocationProductNormalizationReduction
      M n hn2 htb hns D) :
    PiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
      M n hn2 htb hns D := by
  intro S hSlen hadm
  change ∀ (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D).length →
        List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)),
      (∀ i, ∀ v ∈ alloc i, v ∈ S) →
        zeroProfileBooleanNormalize
          (Finset.univ.prod (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
              M n hn2 htb hns D).length =>
            iterDerivList (alloc i)
              (piPlusBooleanProjectedTransformedConstraintFactors
                M n hn2 htb hns D)[i.val])) ∈
          Submodule.span ℚ
            (distribDerivProds Finset.univ
              (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
                  M n hn2 htb hns D).length =>
                (piPlusBooleanProjectedTransformedConstraintFactors
                  M n hn2 htb hns D)[i.val]) S)
  intro alloc halloc
  exact allocatedProduct_mem_span_of_normalizesToDistributedGenerator
    M n hn2 htb hns D S alloc (hred S hSlen hadm alloc halloc)

/-- Paper-scale product/factor normalization reduction. -/
abbrev PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedAllocationProductNormalizationReduction
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)

/-- Paper-scale allocation-level stability from the product/factor normalization
reduction. -/
theorem paperScale_allocationStability_of_productNormalizationReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hred : PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedDistributedGeneratorBooleanStabilityAllocation
      M htb hns :=
  allocationStability_of_productNormalizationReduction
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) hred

/-- Commutation plus product/factor normalization reduction reassemble into the
normalized derivative criterion. -/
theorem paperScale_normalizedDerivativeCriterion_of_commutation_and_productNormalizationReduction
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hred : PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns) :
    PaperScalePiPlusBooleanProjectedNormalizedDerivativeCriterion M htb hns :=
  paperScale_normalizedDerivativeCriterion_of_commutation_and_allocationStability
    M htb hns hcomm
    (paperScale_allocationStability_of_productNormalizationReduction
      M htb hns hred)

/-- Final envelope closeout using the product/factor normalization reduction as
the Boolean-stability input. -/
theorem no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_localFactorReduction_routeBEnvelope_npInclusion
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hcomm : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
      M htb hns)
    (hprod : PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns)
    (hlocal : PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns)
    (henv : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns)
    (hnp : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_allocationStability_localFactorReduction_routeBEnvelope_npInclusion
    M htb hns hcomm
    (paperScale_allocationStability_of_productNormalizationReduction
      M htb hns hprod)
    hlocal henv hnp

/-- Compact closeout package with product/factor normalization as the remaining
Boolean-stability target. -/
structure PaperScalePiPlusBooleanProjectedOneOneProductNormalizationCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  commutation : PaperScalePiPlusBooleanProjectedNormalizedDerivativeCommutation
    M htb hns
  product_normalization :
    PaperScalePiPlusBooleanProjectedAllocationProductNormalizationReduction
      M htb hns
  local_factor_to_allocation :
    PaperScalePiPlusBooleanProjectedOneOneLocalFactorToAllocationReduction
      M htb hns
  routeB_envelope : PaperScaleRouteBSATWindowedIncPSideRankEnvelopeOneOne M htb hns
  np_subspace_inclusion : PaperScalePiPlusBooleanProjectedNPWindowSubspaceInclusion
    M htb hns

/-- The product-normalization closeout package rules out a SAT decider. -/
theorem no_decidesSAT_at_paperScale_of_oneOneProductNormalizationCloseoutInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinputs : PaperScalePiPlusBooleanProjectedOneOneProductNormalizationCloseoutInputs
      M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_localFactorReduction_routeBEnvelope_npInclusion
    M htb hns hinputs.commutation hinputs.product_normalization
    hinputs.local_factor_to_allocation hinputs.routeB_envelope
    hinputs.np_subspace_inclusion

/-! ## Axiom audit anchors -/

#print axioms allocatedProduct_mem_span_of_normalizesToDistributedGenerator
#print axioms allocationStability_of_productNormalizationReduction
#print axioms paperScale_allocationStability_of_productNormalizationReduction
#print axioms paperScale_normalizedDerivativeCriterion_of_commutation_and_productNormalizationReduction
#print axioms no_decidesSAT_at_paperScale_of_commutation_productNormalizationReduction_localFactorReduction_routeBEnvelope_npInclusion
#print axioms no_decidesSAT_at_paperScale_of_oneOneProductNormalizationCloseoutInputs

end PallLean.Paper93.DeepMath.PathC
