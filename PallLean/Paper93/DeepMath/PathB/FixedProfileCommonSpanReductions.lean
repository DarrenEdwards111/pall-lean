import PallLean.Paper93.Direct.TransitionRightDormant

/-!
# Fixed-profile common-span reductions

This file packages kernel-checked reductions around the fixed-profile target

`WithinProfileBound.CookLevinAllBoundedProfileCommonSpanAtProfile`.

It keeps the genuinely live content on admissible, non-dormant profiles:

* non-admissible profiles close by the existing zero-span lemma;
* a fixed-profile admissible-case hypothesis closes the unrestricted profile;
* profiles with positive dormant `transitionRight` mass close vacuously because
  `transitionRight_vacuous` rules out any compiled factor of that type.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulSeparation
open SymmetricPowerBound
open TuringMachine (DTM)
open WithinProfileBound
open PallLean.Paper93.Direct (transitionRight_vacuous)

/-! ## Non-admissible and admissible-only reductions -/

/-- PathB-facing alias for the existing fixed-profile non-admissible closure.

If `profileMass h > Nat.log 2 n`, then the underlying
`allBoundedProfilePostSpan` is `⊥`, so the empty finite family witnesses
`CookLevinAllBoundedProfileCommonSpanAtProfile`. -/
theorem cookLevinAllBoundedProfileCommonSpanAtProfile_nonadmissible_closed
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (h : ProfileHistogram)
    (hnot : ¬ ProfileAdmissible (Nat.log 2 n) h) :
    CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h :=
  cookLevinAllBoundedProfileCommonSpanAtProfile_of_not_admissible
    M n hn htb hns h hnot

/-- Fixed-profile admissible-only reduction.

To prove `CookLevinAllBoundedProfileCommonSpanAtProfile` for one profile `h`,
it is enough to prove it under the explicit admissibility assumption; the
non-admissible branch is closed by
`cookLevinAllBoundedProfileCommonSpanAtProfile_nonadmissible_closed`. -/
theorem cookLevinAllBoundedProfileCommonSpanAtProfile_of_admissible_case
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (h : ProfileHistogram)
    (hadmCase :
      ProfileAdmissible (Nat.log 2 n) h →
        CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h) :
    CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h := by
  by_cases hadm : ProfileAdmissible (Nat.log 2 n) h
  · exact hadmCase hadm
  · exact cookLevinAllBoundedProfileCommonSpanAtProfile_nonadmissible_closed
      M n hn htb hns h hadm

/-- All-profile common-span reduction from admissible profiles only.

This is the common-span analogue of the existing admissible-only
template-collapse reduction, stated directly for
`CookLevinAllBoundedProfileCommonSpanLemma`. -/
theorem cookLevinAllBoundedProfileCommonSpanLemma_of_fixedProfile_admissible_cases
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hadmCases :
      ∀ h : ProfileHistogram, ProfileAdmissible (Nat.log 2 n) h →
        CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h) :
    CookLevinAllBoundedProfileCommonSpanLemma M n hn htb hns := by
  intro h
  exact cookLevinAllBoundedProfileCommonSpanAtProfile_of_admissible_case
    M n hn htb hns h (hadmCases h)

/-! ## Dormant `transitionRight` profile reductions -/

private def zeroBoundedProfile (κ : Nat) : BoundedProfile κ :=
  ⟨fun _ => 0, by
    intro _
    exact Nat.zero_le κ⟩

/-- The canonical Cook-Levin derivative-count profile has zero mass in the
dormant `transitionRight` coordinate.

This is exactly where the proof consumes
`PallLean.Paper93.Direct.transitionRight_vacuous`: the subtype indexed by
compiled factors of type `transitionRight` is empty. -/
theorem derivCountProfile_transitionRight_eq_zero_of_transitionRight_vacuous
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (d : Fin (cookLevinFactorList M n hn htb hns).length → List (Fin n)) :
    derivCountProfile (cookLevinConstraintType M n hn htb hns) d
        ConstraintType.transitionRight = 0 := by
  unfold derivCountProfile
  apply Finset.sum_eq_zero
  intro i _hi
  exfalso
  exact transitionRight_vacuous
    M n hn htb hns hn4 (zeroBoundedProfile (Nat.log 2 n))
    i.val i.property

/-- A fixed profile with nonzero dormant `transitionRight` mass has zero
all-bounded post-span for the actual Cook-Levin factor family. -/
theorem allBoundedProfilePostSpan_zero_of_transitionRight_ne_zero
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4) (h : ProfileHistogram)
    (htr : h ConstraintType.transitionRight ≠ 0) :
    allBoundedProfilePostSpan
      (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (cookLevinConstraintType M n hn htb hns)
      h = ⊥ := by
  rw [eq_bot_iff]
  apply Submodule.span_le.mpr
  intro q hq
  simp only [Set.mem_iUnion, Set.mem_image] at hq
  obtain ⟨_S, _hS, _shift, _hshift, _g, hg, rfl⟩ := hq
  exfalso
  rcases hg with ⟨d, _hd_elts, _hg_eq, hprof, _hlen⟩
  have hz :=
    derivCountProfile_transitionRight_eq_zero_of_transitionRight_vacuous
      M n hn htb hns hn4 d
  have hhzero : h ConstraintType.transitionRight = 0 := by
    rw [← hprof]
    exact hz
  exact htr hhzero

/-- Dormant `transitionRight` fixed-profile common-span closure.

If `h transitionRight ≠ 0`, no bounded classified Cook-Levin generator can
have profile `h`, so the all-bounded post-span is `⊥` and the empty family is a
valid common-span witness. -/
theorem cookLevinAllBoundedProfileCommonSpanAtProfile_of_transitionRight_ne_zero
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4) (h : ProfileHistogram)
    (htr : h ConstraintType.transitionRight ≠ 0) :
    CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h := by
  refine ⟨∅, by simp, ?_⟩
  rw [allBoundedProfilePostSpan_zero_of_transitionRight_ne_zero
    M n hn htb hns hn4 h htr]
  exact bot_le

/-- Positive dormant `transitionRight` mass is a common special case of the
nonzero dormant-profile closure. -/
theorem cookLevinAllBoundedProfileCommonSpanAtProfile_of_transitionRight_pos
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4) (h : ProfileHistogram)
    (htr : 0 < h ConstraintType.transitionRight) :
    CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h :=
  cookLevinAllBoundedProfileCommonSpanAtProfile_of_transitionRight_ne_zero
    M n hn htb hns hn4 h (Nat.ne_of_gt htr)

/-! ## Axiom audit anchors -/

#print axioms cookLevinAllBoundedProfileCommonSpanAtProfile_nonadmissible_closed
#print axioms cookLevinAllBoundedProfileCommonSpanAtProfile_of_admissible_case
#print axioms cookLevinAllBoundedProfileCommonSpanLemma_of_fixedProfile_admissible_cases
#print axioms derivCountProfile_transitionRight_eq_zero_of_transitionRight_vacuous
#print axioms allBoundedProfilePostSpan_zero_of_transitionRight_ne_zero
#print axioms cookLevinAllBoundedProfileCommonSpanAtProfile_of_transitionRight_ne_zero
#print axioms cookLevinAllBoundedProfileCommonSpanAtProfile_of_transitionRight_pos

end PallLean.Paper93.DeepMath.PathB
