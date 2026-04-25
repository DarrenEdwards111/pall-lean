import PallLean.Paper93.DeepMath.PathB.CommonSpanAdmissibleFrontier
import PallLean.Paper93.DeepMath.PathB.FixedProfileCommonSpanReductions
import PallLean.Paper93.DeepMath.PathB.FixedProfileZeroHistogram

/-!
# Common-span profile case split

This file packages the live fixed-profile common-span frontier after the
currently checked formal closures:

* non-admissible histograms close by the existing zero-span theorem;
* histograms with nonzero dormant `transitionRight` mass close by the concrete
  Cook-Levin dormancy theorem;
* the zero histogram reduces to the shifted-base-product common-span blocker.

The remaining named obligation is exactly the admissible,
`transitionRight = 0`, nonzero histogram case.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulSeparation
open SymmetricPowerBound
open TuringMachine (DTM)
open WithinProfileBound

/-- Fixed-profile common-span obligation for the only remaining live profile
case after the checked closures: admissible, zero dormant `transitionRight`
mass, and not the all-zero histogram. -/
def CookLevinAllBoundedProfileCommonSpanLiveProfileCase
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (h : ProfileHistogram) : Prop :=
  ProfileAdmissible (Nat.log 2 n) h →
    h ConstraintType.transitionRight = 0 →
      h ≠ zeroProfileHistogram →
        CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h

/-- All-profile package of the remaining live common-span cases. -/
def CookLevinAllBoundedProfileCommonSpanLiveProfileCases
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ h : ProfileHistogram,
    CookLevinAllBoundedProfileCommonSpanLiveProfileCase M n hn htb hns h

/-- Pointwise case split for `CookLevinAllBoundedProfileCommonSpanAtProfile`.

After importing the existing closures, a fixed profile is reduced to the live
admissible/`transitionRight = 0`/nonzero case plus the zero-histogram
shift-common-span blocker. -/
theorem cookLevinAllBoundedProfileCommonSpanAtProfile_of_liveProfileCase
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns)
    (h : ProfileHistogram)
    (hlive :
      CookLevinAllBoundedProfileCommonSpanLiveProfileCase
        M n hn htb hns h) :
    CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h := by
  by_cases hadm : ProfileAdmissible (Nat.log 2 n) h
  · by_cases htr : h ConstraintType.transitionRight = 0
    · by_cases hz : h = zeroProfileHistogram
      · simpa [hz] using
          cookLevinAllBoundedProfileCommonSpanAtProfile_zero_of_shiftCommonSpan
            M n hn htb hns hzero
      · exact hlive hadm htr hz
    · exact
        cookLevinAllBoundedProfileCommonSpanAtProfile_of_transitionRight_ne_zero
          M n hn htb hns hn4 h htr
  · exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_nonadmissible_closed
        M n hn htb hns h hadm

/-- The named live profile package, together with the zero-histogram
shift-common-span blocker, proves the full all-profile all-bounded common-span
lemma. -/
theorem cookLevinAllBoundedProfileCommonSpanLemma_of_liveProfileCases
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns)
    (hlive :
      CookLevinAllBoundedProfileCommonSpanLiveProfileCases
        M n hn htb hns) :
    CookLevinAllBoundedProfileCommonSpanLemma M n hn htb hns := by
  intro h
  exact
    cookLevinAllBoundedProfileCommonSpanAtProfile_of_liveProfileCase
      M n hn htb hns hn4 hzero h (hlive h)

/-- The same case split closes the active per-`S`/shift common-span blocker
through the existing all-span bridge. -/
theorem cookLevinBoundedProfileCommonSpanLemma_of_liveProfileCases
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns)
    (hlive :
      CookLevinAllBoundedProfileCommonSpanLiveProfileCases
        M n hn htb hns) :
    CookLevinBoundedProfileCommonSpanLemma M n hn htb hns :=
  cookLevinBoundedProfileCommonSpan_of_allBoundedProfileCommonSpan
    M n hn htb hns
    (cookLevinAllBoundedProfileCommonSpanLemma_of_liveProfileCases
      M n hn htb hns hn4 hzero hlive)

/-! ## Axiom audit anchors -/

#print axioms cookLevinAllBoundedProfileCommonSpanAtProfile_of_liveProfileCase
#print axioms cookLevinAllBoundedProfileCommonSpanLemma_of_liveProfileCases
#print axioms cookLevinBoundedProfileCommonSpanLemma_of_liveProfileCases

end PallLean.Paper93.DeepMath.PathB
