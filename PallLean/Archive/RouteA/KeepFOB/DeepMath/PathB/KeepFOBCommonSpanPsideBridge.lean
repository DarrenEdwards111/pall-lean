import PallLean.Paper93.DeepMath.PathB.ActiveProfileTemplateCollapseAssembly
import PallLean.Archive.RouteA.KeepFOB.DeepMath.PathB.KeepFOBTemplateCollapseAssembly
import PallLean.Paper93.DeepMath.PathB.ZeroProfileNonScalarClosure
import PallLean.Paper93.DeepMath.PathB.ZeroProfileSupportCardBound
import PallLean.ProfileCompression

set_option exponentiation.threshold 1000

/-!
# keepFOB P-side bridge through non-scalar zero-profile common spans

The zero-profile template route asks for
`profileTemplateBound zeroProfileHistogram = 1`, hence for a singleton span.
`ZeroProfileScalarClosure` proves that scalar/singleton route is false for the
actual Cook-Levin base product.

This file records the honest replacement route that avoids the singleton
zero-profile bottleneck:

* use a non-scalar `CookLevinZeroHistogramShiftCommonSpan`, with cardinality
  bounded only by `withinProfileBound (Nat.log 2 n)`;
* combine it with active-profile type cases to obtain
  `CookLevinExactWithinProfileFinrankLemma`;
* use the exact-within-profile P-side theorem from `ProfileCompression`;
* transport the resulting unprojected bound through keepFOB rank monotonicity.

This is P-side progress only.  It does not prove the remaining support-card
arithmetic side condition.
-/

namespace PallLean
namespace Paper93
namespace DeepMath
namespace PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open SymmetricPowerBound
open TuringMachine
open WithinProfileBound

private theorem ge_four_of_ge_two_pow_804_common {n : Nat} (hn : n ≥ 2 ^ 804) :
    n ≥ 4 := by
  have hfour : (4 : Nat) ≤ 2 ^ 804 := by
    calc
      (4 : Nat) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  exact le_trans hfour hn

/-- Exact within-profile rank is enough for the P-side field of any
rank-monotone SAT-decider gauge. -/
theorem satDeciderGaugePSideBound_of_exactWithinProfileLemma
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (gauge : SATDeciderGaugeMap M n hn2 htb hns)
    (hrank : SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge)
    (hexact :
      CookLevinExactWithinProfileFinrankLemma M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns gauge :=
  satDeciderGaugePSideBound_of_rankMonotone_of_unprojected_bound
    M n hn2 htb hns gauge hrank
    (ProfileCompression.p_side_rank_bound_for_cook_levin_of_exactWithinProfileLemma
      M n hn2 htb hns hexact)

/-- For keepFOB, active type cases plus a non-scalar zero-profile common span
fill the P-side field. -/
theorem satDeciderGaugeKeepFOBProjection_pSideBound_of_activeTypeCases_zeroCommonSpan
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) :=
  satDeciderGaugePSideBound_of_exactWithinProfileLemma
    M n hn2 htb hns
    (satDeciderGaugeKeepFOBProjection M n hn2 htb hns)
    (satDeciderGaugeKeepFOBProjection_rankMonotonicity M n hn2 htb hns)
    (cookLevinExactWithinProfileFinrankLemma_of_activeTypeCaseBlockers_and_zeroProfileCommonSpan
      M n hn2 htb hns (ge_four_of_ge_two_pow_804_common hn) hzero hblock)

/-- The non-scalar common-span route packages the full keepFOB rich projection
target once active type cases are supplied. -/
theorem cookLevinRichProjectionTarget_of_keepFOB_activeTypeCases_zeroCommonSpan
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  ⟨satDeciderGaugeKeepFOBProjection M n hn2 htb hns,
    satDeciderGaugeKeepFOBProjection_rankMonotonicity M n hn2 htb hns,
    satDeciderGaugeKeepFOBProjection_pSideBound_of_activeTypeCases_zeroCommonSpan
      M n hn hn2 htb hns hzero hblock,
    satDeciderGaugeKeepFOBProjection_npIdentityMinorPreservation
      M n hn hn2 htb hns⟩

/-- A budgeted non-scalar zero-profile closure is enough for the keepFOB
P-side route once its budget fits inside `withinProfileBound`. -/
theorem cookLevinRichProjectionTarget_of_keepFOB_activeTypeCases_zeroNonScalarClosure
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {budget : Nat}
    (hzero :
      CookLevinZeroProfileNonScalarClosureWithBudget M n hn2 htb hns budget)
    (hbudget : budget ≤ withinProfileBound (Nat.log 2 n))
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_keepFOB_activeTypeCases_zeroCommonSpan
    M n hn hn2 htb hns
    (cookLevinZeroHistogramShiftCommonSpan_of_nonScalarClosureWithBudget
      M n hn2 htb hns hzero hbudget)
    hblock

/-- Concrete finite-support cardinal arithmetic for the zero profile is enough
to feed the non-scalar keepFOB common-span route. -/
theorem cookLevinRichProjectionTarget_of_keepFOB_activeTypeCases_zeroSupportCardSum
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hzero :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn2 htb hns)
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_keepFOB_activeTypeCases_zeroCommonSpan
    M n hn hn2 htb hns
    (cookLevinZeroHistogramShiftCommonSpan_of_nonScalarSupportCardSumSideCondition
      M n hn2 htb hns hzero)
    hblock

/-- Uniform discharge form of the non-scalar common-span route. -/
theorem cookLevinRichProjectionDischarge_of_keepFOB_activeTypeCases_zeroCommonSpan
    (hzero :
      ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroHistogramShiftCommonSpan M n hn2 htb hns)
    (hblock :
      ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    CookLevinRichProjectionDischarge := by
  intro M n hn hn2 htb hns _hdec
  exact
    cookLevinRichProjectionTarget_of_keepFOB_activeTypeCases_zeroCommonSpan
      M n hn hn2 htb hns
      (hzero M n hn2 htb hns)
      (hblock M n hn2 htb hns)

/-- Uniform discharge form from the concrete support-card sum side condition. -/
theorem cookLevinRichProjectionDischarge_of_keepFOB_activeTypeCases_zeroSupportCardSum
    (hzero :
      ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinZeroProfileSupportCardSumSideCondition M n hn2 htb hns)
    (hblock :
      ∀ (M : DTM) (n : Nat) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        CookLevinActiveProfileTypeCaseBlockers M n hn2 htb hns) :
    CookLevinRichProjectionDischarge := by
  intro M n hn hn2 htb hns hdec
  exact
    cookLevinRichProjectionTarget_of_keepFOB_activeTypeCases_zeroSupportCardSum
      M n hn hn2 htb hns
      (hzero M n hn2 htb hns)
      (hblock M n hn2 htb hns)

/-! ## Axiom audit anchors -/

#print axioms satDeciderGaugePSideBound_of_exactWithinProfileLemma
#print axioms satDeciderGaugeKeepFOBProjection_pSideBound_of_activeTypeCases_zeroCommonSpan
#print axioms cookLevinRichProjectionTarget_of_keepFOB_activeTypeCases_zeroCommonSpan
#print axioms cookLevinRichProjectionTarget_of_keepFOB_activeTypeCases_zeroNonScalarClosure
#print axioms cookLevinRichProjectionTarget_of_keepFOB_activeTypeCases_zeroSupportCardSum
#print axioms cookLevinRichProjectionDischarge_of_keepFOB_activeTypeCases_zeroCommonSpan
#print axioms cookLevinRichProjectionDischarge_of_keepFOB_activeTypeCases_zeroSupportCardSum

end PathB
end DeepMath
end Paper93
end PallLean
