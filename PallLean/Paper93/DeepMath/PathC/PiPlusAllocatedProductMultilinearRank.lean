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
open WithinProfileBound
open SymmetricPowerBound

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


/-! ## Raw allocated-product rank from a finite profile cover

The normalization handoff above leaves the real P-side cost at the raw row
space of the allocated derivative product.  The next lemmas isolate the exact
linear-algebra closeout needed after the Leibniz/profile work: if every raw
SPDP generator row is covered by a finite sum of profile-compressed spaces, and
each such space has the Lemma-31 dimension budget, then the raw rank is bounded
by `number_of_spaces * withinProfileBound κ`.
-/

/-- Kernel-clean finite-cover rank bound for raw SPDP rows.  This is just
`Submodule.finrank_mono` followed by the finite `iSup` dimension inequality and
the per-summand dimension budgets. -/
theorem rawRank_le_sum_subspaces_of_rawSubspace_le {N r : Nat}
    (B : BlockPartition N) (κ ℓ C : Nat)
    (p : MvPolynomial (Fin N) ℚ)
    (W : Fin r → Submodule ℚ (MvPolynomial (Fin N) ℚ))
    [∀ i, Module.Finite ℚ (W i)]
    (hcover : rawBlockedSpdpSubspace B κ ℓ p ≤ ⨆ i : Fin r, W i)
    (hdim : ∀ i : Fin r, Module.finrank ℚ (W i) ≤ C) :
    rkSPDP B κ ℓ p ≤ r * C := by
  unfold rkSPDP rawBlockedSpdpRank
  calc
    Module.finrank ℚ (rawBlockedSpdpSubspace B κ ℓ p)
        ≤ Module.finrank ℚ ↥(⨆ i : Fin r, W i) :=
          Submodule.finrank_mono hcover
    _ ≤ ∑ i : Fin r, Module.finrank ℚ (W i) :=
          finrank_iSup_fin_le r W
    _ ≤ ∑ _i : Fin r, C :=
          Finset.sum_le_sum (fun i _hi => hdim i)
    _ = r * C := by
          simp [Finset.sum_const]

/-- Generator-row form of `rawRank_le_sum_subspaces_of_rawSubspace_le`: it is
enough to classify each raw generator `m * ∂_S p` into the finite profile cover.
This is the form consumed by a Leibniz expansion proof. -/
theorem rawRank_le_sum_subspaces_of_generator_rows {N r : Nat}
    (B : BlockPartition N) (κ ℓ C : Nat)
    (p : MvPolynomial (Fin N) ℚ)
    (W : Fin r → Submodule ℚ (MvPolynomial (Fin N) ℚ))
    [∀ i, Module.Finite ℚ (W i)]
    (hrow : ∀ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible B S →
      m * iterDerivList S p ∈ ⨆ i : Fin r, W i)
    (hdim : ∀ i : Fin r, Module.finrank ℚ (W i) ≤ C) :
    rkSPDP B κ ℓ p ≤ r * C := by
  refine rawRank_le_sum_subspaces_of_rawSubspace_le B κ ℓ C p W ?_ hdim
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, m, hSlen, hmdeg, hmvars, hadm, rfl⟩
  exact hrow S m hSlen hmdeg hmvars hadm

/-- Allocated-product specialization with a Lemma-31-style budget.  Once the
Leibniz expansion plus per-factor/profile compression proves the generator-row
cover into `W`, the raw rank of the allocated derivative product is bounded by
`r * withinProfileBound κ`. -/
theorem allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows
    {r : Nat}
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (W : Fin r → Submodule ℚ
      (MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))
    [∀ i, Module.Finite ℚ (W i)]
    (hrow : ∀
      (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible B S →
      m * iterDerivList S
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ∈ ⨆ i : Fin r, W i)
    (hdim : ∀ i : Fin r, Module.finrank ℚ (W i) ≤ withinProfileBound κ) :
    rkSPDP B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ≤
      r * withinProfileBound κ := by
  exact rawRank_le_sum_subspaces_of_generator_rows B κ ℓ (withinProfileBound κ)
    (piPlusBooleanProjectedAllocatedDerivativeProduct M n hn2 htb hns D alloc)
    W hrow hdim

/-- Paper-scale name for the allocated-product raw rank target.  The only
remaining mathematical input is the `hrow` classifier: expand raw rows by
Leibniz, classify each per-factor derivative into its local span, place each
summand in one of the finite profile-compressed spaces `W`, then use Lemma 31 to
discharge `hdim`. -/
theorem paperScale_allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows
    {r : Nat}
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (κ ℓ : Nat)
    (W : Fin r → Submodule ℚ
      (MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ))
    [∀ i, Module.Finite ℚ (W i)]
    (hrow : ∀
      (S : List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
      (m : MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition S →
      m * iterDerivList S
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc) ∈
        ⨆ i : Fin r, W i)
    (hdim : ∀ i : Fin r, Module.finrank ℚ (W i) ≤ withinProfileBound κ) :
    rkSPDP
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc) ≤
      r * withinProfileBound κ := by
  exact allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    alloc
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ W hrow hdim

/-! ## Axiom audit anchors -/

#print axioms multilinearize_allocatedDerivativeProduct_eq_normalizedFactorProduct
#print axioms allocatedNormalizedFactorProduct_multilinearizedRank_le_rawAllocatedProductRank
#print axioms rawRank_le_sum_subspaces_of_rawSubspace_le
#print axioms rawRank_le_sum_subspaces_of_generator_rows
#print axioms allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows
#print axioms paperScale_allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
