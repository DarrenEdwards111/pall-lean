import PallLean.Paper93.DeepMath.PathC.PiPlusDistributedStabilityAllocationFactors
import PallLean.Paper93.DeepMath.PathC.PiPlusPaperRemark21MultilinearizeRank

/-!
# Allocated product normalization at the rank level

This file composes the exact allocated-product Boolean normalization theorem with
Remark 21's rank-level multilinearization inequality.  The point is deliberately
narrow: the normalized factor product is the Boolean representative of the
allocated derivative product, while the rank bound is paid for at the raw
allocated-product row space.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- The normalized product of the individually normalized allocated derivative
factors, kept as an expression-level abbreviation so later row-certificate
lemmas can point to the exact product that appears after quotient
normalization. -/
noncomputable abbrev piPlusBooleanProjectedAllocatedNormalizedFactorProduct
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ :=
  Finset.univ.prod (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
      M n hn2 htb hns D).length =>
    zeroProfileBooleanNormalize
      (iterDerivList (alloc i)
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D)[i.val]))

/-- Exact Boolean-representative statement for the allocated Leibniz product:
multilinearizing the allocated derivative product is the same Boolean object as
multilinearizing the product of the normalized local derivative factors. -/
theorem multilinearize_allocatedDerivativeProduct_eq_normalizedFactorProduct
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    multilinearize
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) =
      multilinearize
        (piPlusBooleanProjectedAllocatedNormalizedFactorProduct
          M n hn2 htb hns D alloc) := by
  apply BoolPoly.ext
  simp only [coe_multilinearize]
  exact zeroProfileBooleanNormalize_allocatedDerivativeProduct_eq_normalizedFactorProduct
    M n hn2 htb hns D alloc

/-- Rank-level form of the previous equality plus Remark 21.  The normalized
factor product is identified as the Boolean representative, but the SPDP rank
cost is bounded by the raw allocated-product row space.  This is the exact
normalization/rank handoff needed before the remaining Booleanity row
certificate synthesis. -/
theorem allocatedNormalizedFactorProduct_multilinearizedRank_le_rawAllocatedProductRank
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : ℕ) :
    multilinearize
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) =
      multilinearize
        (piPlusBooleanProjectedAllocatedNormalizedFactorProduct
          M n hn2 htb hns D alloc) ∧
    rkSPDP_multilinearized B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ≤
      rkSPDP B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) := by
  exact ⟨
    multilinearize_allocatedDerivativeProduct_eq_normalizedFactorProduct
      M n hn2 htb hns D alloc,
    multilinearize_rank_le_direct B κ ℓ
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc)⟩

/-! ## Axiom audit anchors -/

#print axioms multilinearize_allocatedDerivativeProduct_eq_normalizedFactorProduct
#print axioms allocatedNormalizedFactorProduct_multilinearizedRank_le_rawAllocatedProductRank

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
