import PallLean.WithinProfileBound

/-!
# Admissible-only common-span frontier

This file mirrors the existing admissible-only reductions for
`CookLevinProfileTemplateCollapseLemma`, but for the smaller fixed-profile
common-span target `CookLevinAllBoundedProfileCommonSpanAtProfile`.

The point is to remove the non-admissible profile branch from the live P-side
frontier.  Non-admissible profiles are already zero by
`allBoundedProfilePostSpan_zero_of_not_admissible`; the remaining content is
therefore exactly the admissible fixed-profile span.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open PaperFaithfulSeparation
open WithinProfileBound
open SymmetricPowerBound

/-- Admissible-only version of the all-bounded common-span lemma. -/
def CookLevinAllBoundedProfileCommonSpanLemmaAdmissibleOnly
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ h : ProfileHistogram, ProfileAdmissible (Nat.log 2 n) h →
    CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h

/-- Bounded-profile version of the all-bounded common-span lemma. -/
def CookLevinAllBoundedProfileCommonSpanLemmaBoundedProfile
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ bp : BoundedProfile (Nat.log 2 n),
    CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns
      bp.toHistogram

/-- Fixed-profile admissible-only reducer for the all-bounded common-span
target.  This is the smallest form of the admissibility split: prove the
profile if it is admissible; otherwise the existing zero-span theorem closes
the branch. -/
theorem cookLevinAllBoundedProfileCommonSpanAtProfile_of_admissibleOnly
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (h : ProfileHistogram)
    (hcase :
      ProfileAdmissible (Nat.log 2 n) h →
        CookLevinAllBoundedProfileCommonSpanAtProfile
          M n hn htb hns h) :
    CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h := by
  by_cases hadm : ProfileAdmissible (Nat.log 2 n) h
  · exact hcase hadm
  · exact cookLevinAllBoundedProfileCommonSpanAtProfile_of_not_admissible
      M n hn htb hns h hadm

/-- Admissible-only common-span data gives the full all-profile common-span
lemma; non-admissible profiles are discharged by the existing zero-span
theorem. -/
theorem cookLevinAllBoundedProfileCommonSpanLemma_of_admissibleOnly
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hadm :
      CookLevinAllBoundedProfileCommonSpanLemmaAdmissibleOnly
        M n hn htb hns) :
    CookLevinAllBoundedProfileCommonSpanLemma M n hn htb hns := by
  intro h
  exact cookLevinAllBoundedProfileCommonSpanAtProfile_of_admissibleOnly
    M n hn htb hns h (hadm h)

/-- Bounded-profile common-span data gives the admissible-only common-span
frontier because every admissible histogram is componentwise bounded by
`Nat.log 2 n`. -/
theorem cookLevinAllBoundedProfileCommonSpanLemmaAdmissibleOnly_of_boundedProfile
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbp :
      CookLevinAllBoundedProfileCommonSpanLemmaBoundedProfile
        M n hn htb hns) :
    CookLevinAllBoundedProfileCommonSpanLemmaAdmissibleOnly
      M n hn htb hns := by
  intro h hadm
  let bp : BoundedProfile (Nat.log 2 n) :=
    ⟨h, admissible_implies_bounded hadm⟩
  exact hbp bp

/-- Bounded-profile common-span data gives the full all-profile common-span
lemma. -/
theorem cookLevinAllBoundedProfileCommonSpanLemma_of_boundedProfile
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbp :
      CookLevinAllBoundedProfileCommonSpanLemmaBoundedProfile
        M n hn htb hns) :
    CookLevinAllBoundedProfileCommonSpanLemma M n hn htb hns :=
  cookLevinAllBoundedProfileCommonSpanLemma_of_admissibleOnly
    M n hn htb hns
    (cookLevinAllBoundedProfileCommonSpanLemmaAdmissibleOnly_of_boundedProfile
      M n hn htb hns hbp)

/-- Bounded-profile common-span data closes the active per-`S`/shift
common-span blocker through the existing all-span bridge. -/
theorem cookLevinBoundedProfileCommonSpanLemma_of_allBoundedProfile_boundedProfile
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hbp :
      CookLevinAllBoundedProfileCommonSpanLemmaBoundedProfile
        M n hn htb hns) :
    CookLevinBoundedProfileCommonSpanLemma M n hn htb hns :=
  cookLevinBoundedProfileCommonSpan_of_allBoundedProfileCommonSpan
    M n hn htb hns
    (cookLevinAllBoundedProfileCommonSpanLemma_of_boundedProfile
      M n hn htb hns hbp)

/-! ## Axiom audit anchors -/

#print axioms cookLevinAllBoundedProfileCommonSpanLemma_of_admissibleOnly
#print axioms cookLevinAllBoundedProfileCommonSpanAtProfile_of_admissibleOnly
#print axioms cookLevinAllBoundedProfileCommonSpanLemmaAdmissibleOnly_of_boundedProfile
#print axioms cookLevinAllBoundedProfileCommonSpanLemma_of_boundedProfile
#print axioms cookLevinBoundedProfileCommonSpanLemma_of_allBoundedProfile_boundedProfile

end PallLean.Paper93.DeepMath.PathB
