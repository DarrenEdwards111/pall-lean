import PallLean.Paper93.DeepMath.PathC.PiPlusOneWindowZeroProfileRowMap

/-!
# Obstruction to the identity one-window zero-profile containment

`CookLevinOneWindowZeroProfilePostSpanContainment` is too strong at paper scale:
combined with the finite-dimensional concrete zero-profile subspace, it would
recreate the old unprojected one-window zero common-span socket, which has
already been proved impossible.  This file removes that false target from the
live frontier.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PallLean.Paper93.Wiring
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- A one-window zero-profile containment into the concrete zero-profile
subspace would imply the old unprojected one-window zero common-span socket. -/
theorem cookLevinOneWindowZeroCommonSpan_of_zeroProfilePostSpanContainment
    (M : DTM) (n : Nat) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hpost : CookLevinOneWindowZeroProfilePostSpanContainment
      M n hn htb hns hn4) :
    CookLevinOneWindowZeroHistogramShiftCommonSpan M n hn htb hns := by
  classical
  have hW_fin :
      ∀ τ, Module.Finite ℚ ↥(concreteWCanonical n hn4 τ) := by
    intro τ
    simpa [concreteWCanonical] using
      concreteW_finite n hn4 (Fin.castLEEmb hn4) τ
  have hW_dim :
      ∀ τ, Module.finrank ℚ ↥(concreteWCanonical n hn4 τ) ≤ 3 := by
    intro τ
    simpa [concreteWCanonical] using
      concreteW_finrank_le_three n hn4 (Fin.castLEEmb hn4) τ
  haveI hfin : Module.Finite ℚ
      ↥(profileSubspace zeroProfileHistogram (concreteWCanonical n hn4)) :=
    profileSubspace_finite_of_finite zeroProfileHistogram
      (concreteWCanonical n hn4) hW_fin
  rcases finite_submodule_le_span_finset_card_le_finrank
      (profileSubspace zeroProfileHistogram (concreteWCanonical n hn4)) with
    ⟨G, hGspan, hGcard⟩
  refine ⟨G, ?_, ?_⟩
  · have hbound := profileSubspace_finrank_bound
      (Iface := ConstraintType) zeroProfileHistogram
      (concreteWCanonical n hn4) hW_fin hW_dim
    exact le_trans hGcard
      (le_trans (by simpa [profileTemplateBound] using hbound)
        (profileTemplateBound_le_withinProfileBound
          (Nat.log 2 n + 1) zeroProfileHistogram
          (zeroProfileHistogram_admissible (Nat.log 2 n + 1))))
  · intro q hq
    have hqPost : q ∈
        allBoundedProfilePostSpan
          (cook_levin_compilation M n hn htb hns).partition
          (Nat.log 2 n + 1) (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn htb hns).get i)
          (cookLevinConstraintType M n hn htb hns)
          zeroProfileHistogram := by
      rw [allBoundedProfilePostSpan_zeroProfile_eq_shiftImageSpan
        (cook_levin_compilation M n hn htb hns).partition
        (Nat.log 2 n + 1) (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        (cookLevinConstraintType M n hn htb hns)]
      exact Submodule.subset_span hq
    exact hGspan (hpost hqPost)

/-- Therefore the paper-scale identity one-window zero-profile containment is
impossible.  The zero-profile route must remain genuinely projected/quotiented;
it cannot be closed by an identity concreteW containment. -/
theorem not_paperScale_cookLevinOneWindowZeroProfilePostSpanContainment
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    ¬ CookLevinOneWindowZeroProfilePostSpanContainment
      M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four := by
  intro hpost
  exact not_paperScale_cookLevinOneWindowZeroHistogramShiftCommonSpan
    M htb hns
    (cookLevinOneWindowZeroCommonSpan_of_zeroProfilePostSpanContainment
      M (2 ^ 804) paperScale_ge_two htb hns paperScale_two_pow_804_ge_four hpost)

/-! ## Axiom audit anchors -/

#print axioms cookLevinOneWindowZeroCommonSpan_of_zeroProfilePostSpanContainment
#print axioms not_paperScale_cookLevinOneWindowZeroProfilePostSpanContainment

end PallLean.Paper93.DeepMath.PathC
