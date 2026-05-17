import PallLean.Paper93.DeepMath.PathC.PiPlusRouteBOneWindowMixedFrontier

/-!
# One-window Route B per-type frontier

This file pushes the nonzero active-template half of the corrected one-window
Route B blocker down to a profile-local per-type spanning statement at the
enlarged window `κ = log₂ n + 1`.

The zero profile remains handled by the corrected common-span budget from
`PiPlusRouteBOneWindowMixedFrontier`; only nonzero active profiles need the
per-type/template machinery.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound

attribute [local instance] Classical.dec

/-- One-window profile-local per-type spanning.  This is the `log₂ n + 1`
analogue of `CookLevinPerTypeSpanningAtBoundedProfile`, but it is kept local to
Route C so the older hardcoded `log₂ n` APIs stay untouched. -/
def CookLevinOneWindowPerTypeSpanningAtBoundedProfile
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (bp : BoundedProfile (Nat.log 2 n + 1)) : Prop :=
  ∀ (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n + 1)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (g : MvPolynomial (Fin n) ℚ)
    (_hg : g ∈ boundedProfileClassifiedSet
              (fun i => (cookLevinFactorList M n hn htb hns).get i)
              (cookLevinConstraintType M n hn htb hns)
              S bp.toHistogram),
    mlProj (shift * g) ∈ profileSubspace bp.toHistogram W

/-- Generic finite-dimensionality of the profile subspace.  The existing
Cook-Levin API specializes this to the hardcoded `log₂ n`; the one-window route
needs the same argument at `log₂ n + 1`. -/
theorem profileSubspace_finite_of_finite
    {n : Nat} (h : ProfileHistogram)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ)) :
    Module.Finite ℚ ↥(profileSubspace h W) := by
  classical
  unfold profileSubspace
  set d : ConstraintType → Nat := fun τ => Module.finrank ℚ ↥(W τ) with hd_def
  let b : ∀ τ, Module.Basis (Fin (d τ)) ℚ ↥(W τ) :=
    fun τ => Module.finBasis ℚ ↥(W τ)
  have hle :
      profileSubspace h W ≤
        Submodule.span ℚ
          (Set.range (profileSymProd W b : ProfileIndex h d → _)) :=
    profileSubspace_le_profileSymProd_span W b
  haveI hfin_big : Module.Finite ℚ
      ↥(Submodule.span ℚ
        (Set.range (profileSymProd W b : ProfileIndex h d → _))) := by
    apply Module.Finite.span_of_finite
    exact Set.finite_range _
  exact Module.Finite.of_injective
    ((Submodule.inclusion hle) : _ →ₗ[ℚ] _)
    (Submodule.inclusion_injective hle)

/-- A one-window profile-local per-type spanning statement gives the fixed
profile template-collapse target at that profile. -/
theorem cookLevinWindowedProfileTemplateCollapseAtProfile_one_zero_of_perTypeSpanningAtBoundedProfile
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (bp : BoundedProfile (Nat.log 2 n + 1))
    (hSpanAt :
      CookLevinOneWindowPerTypeSpanningAtBoundedProfile
        M n hn htb hns W bp) :
    CookLevinWindowedProfileTemplateCollapseAtProfile
      1 0 M n hn htb hns bp.toHistogram := by
  classical
  have hpost :
      allBoundedProfilePostSpan
          (cook_levin_compilation M n hn htb hns).partition
          (Nat.log 2 n + 1) (Nat.log 2 n + 0)
          (fun i => (cookLevinFactorList M n hn htb hns).get i)
          (cookLevinConstraintType M n hn htb hns)
          bp.toHistogram
        ≤ profileSubspace bp.toHistogram W := by
    apply Submodule.span_le.mpr
    intro q hq
    simp only [Set.mem_iUnion, Set.mem_image] at hq
    obtain ⟨S, hSlen, shift, hshiftvars, g, hg, rfl⟩ := hq
    exact hSpanAt S hSlen shift hshiftvars g hg
  haveI hfin_V : Module.Finite ℚ ↥(profileSubspace bp.toHistogram W) :=
    profileSubspace_finite_of_finite bp.toHistogram W hW_fin
  rcases finite_submodule_le_span_finset_card_le_finrank
    (profileSubspace bp.toHistogram W) with ⟨G, hGspan, hGcard⟩
  refine ⟨G, ?_, ?_⟩
  · exact le_trans hpost hGspan
  · exact le_trans hGcard
      (by
        have hbound :=
          profileSubspace_finrank_bound
            (Iface := ConstraintType) bp.toHistogram W hW_fin hW_dim
        simpa [profileTemplateBound] using hbound)

/-- Nonzero active one-window per-type spanning cases. -/
def CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)) : Prop :=
  ∀ bp : ActiveAdmissibleProfile (Nat.log 2 n + 1),
    bp.toHistogram ≠ zeroProfileHistogram →
      CookLevinOneWindowPerTypeSpanningAtBoundedProfile
        M n hn htb hns W bp.toActiveBoundedProfile.toBoundedProfile

/-- One-window per-type spanning cases imply the nonzero active template cases. -/
theorem cookLevinOneWindowProfileTemplateCollapseActiveAdmissibleProfileCases_of_perTypeSpanning
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hSpanCases :
      CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases
        M n hn htb hns W) :
    CookLevinOneWindowProfileTemplateCollapseActiveAdmissibleProfileCases
      M n hn htb hns := by
  intro bp hne
  simpa [ActiveAdmissibleProfile.toHistogram,
    ActiveAdmissibleProfile.toActiveBoundedProfile,
    ActiveBoundedProfile.toHistogram,
    ActiveBoundedProfile.toBoundedProfile] using
    cookLevinWindowedProfileTemplateCollapseAtProfile_one_zero_of_perTypeSpanningAtBoundedProfile
      M n hn htb hns W hW_fin hW_dim
      bp.toActiveBoundedProfile.toBoundedProfile
      (hSpanCases bp hne)

/-- Corrected mixed one-window blockers from a zero-profile common-span blocker
and nonzero active per-type spanning. -/
theorem cookLevinOneWindowMixedActiveTemplateBlockers_of_zeroCommonSpan_and_perTypeSpanning
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hzero : CookLevinOneWindowZeroHistogramShiftCommonSpan M n hn htb hns)
    (hSpanCases :
      CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases
        M n hn htb hns W) :
    CookLevinOneWindowMixedActiveTemplateBlockers M n hn htb hns :=
  ⟨hzero,
    cookLevinOneWindowProfileTemplateCollapseActiveAdmissibleProfileCases_of_perTypeSpanning
      M n hn htb hns W hW_fin hW_dim hSpanCases⟩

/-- Final one-window Route-B P-side bound from the corrected zero common-span
blocker plus nonzero active per-type spanning. -/
theorem routeBSATWindowedIncPSideRankBound_one_zero_of_zeroCommonSpan_and_perTypeSpanning
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hzero : CookLevinOneWindowZeroHistogramShiftCommonSpan M n hn htb hns)
    (hSpanCases :
      CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases
        M n hn htb hns W) :
    RouteBSATWindowedIncPSideRankBound 1 0 M n hn htb hns :=
  routeBSATWindowedIncPSideRankBound_one_zero_of_mixedActiveTemplateBlockers
    M n hn htb hns hn4
    (cookLevinOneWindowMixedActiveTemplateBlockers_of_zeroCommonSpan_and_perTypeSpanning
      M n hn htb hns W hW_fin hW_dim hzero hSpanCases)

/-- Paper-scale specialization of the per-type frontier. -/
theorem paperScale_routeBSATWindowedIncPSideRankBound_one_zero_of_zeroCommonSpan_and_perTypeSpanning
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin (2 ^ 804)) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hzero : CookLevinOneWindowZeroHistogramShiftCommonSpan
      M (2 ^ 804) paperScale_ge_two htb hns)
    (hSpanCases :
      CookLevinOneWindowPerTypeSpanningActiveAdmissibleProfileCases
        M (2 ^ 804) paperScale_ge_two htb hns W) :
    RouteBSATWindowedIncPSideRankBound
      1 0 M (2 ^ 804) paperScale_ge_two htb hns :=
  routeBSATWindowedIncPSideRankBound_one_zero_of_zeroCommonSpan_and_perTypeSpanning
    M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four
    W hW_fin hW_dim hzero hSpanCases

/-! ## Axiom audit anchors -/

#print axioms cookLevinWindowedProfileTemplateCollapseAtProfile_one_zero_of_perTypeSpanningAtBoundedProfile
#print axioms cookLevinOneWindowProfileTemplateCollapseActiveAdmissibleProfileCases_of_perTypeSpanning
#print axioms cookLevinOneWindowMixedActiveTemplateBlockers_of_zeroCommonSpan_and_perTypeSpanning
#print axioms routeBSATWindowedIncPSideRankBound_one_zero_of_zeroCommonSpan_and_perTypeSpanning
#print axioms paperScale_routeBSATWindowedIncPSideRankBound_one_zero_of_zeroCommonSpan_and_perTypeSpanning

end PallLean.Paper93.DeepMath.PathC
