import PallLean.WithinProfileBound

/-!
# Fixed all-zero derivative-count profile

This file isolates the admissible all-zero histogram case for the fixed-profile
Cook-Levin common-span/template-collapse frontiers.

The checked content is the exact zero-profile reduction for
`allBoundedProfilePostSpan`: if the derivative-count profile is identically
zero, then every Leibniz distribution uses empty derivative lists, so the only
classified generator before shifting is the base product
`Finset.univ.prod factors`.

The remaining blocker is therefore not the derivative-profile classification;
it is the uniform finite-dimensional control of the shifted family

  `mlProj (shift * Finset.univ.prod factors)`

as `S` and `shift.vars ⊆ S.toFinset` vary with `S.length ≤ κ`.  We expose that
blocker as the theorem-level Prop `CookLevinZeroHistogramShiftCommonSpan`.
-/

namespace PallLean
namespace Paper93
namespace DeepMath
namespace PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP SPDP
open scoped BigOperators

attribute [local instance] Classical.dec

/-- The all-zero derivative-count histogram. -/
def zeroProfileHistogram : ProfileHistogram := fun _ => 0

@[simp] theorem zeroProfileHistogram_apply (τ : ConstraintType) :
    zeroProfileHistogram τ = 0 := rfl

@[simp] theorem profileMass_zeroProfileHistogram :
    profileMass zeroProfileHistogram = 0 := by
  classical
  simp [profileMass, zeroProfileHistogram]

/-- The zero profile is admissible at every radius. -/
theorem zeroProfileHistogram_admissible (κ : ℕ) :
    ProfileAdmissible κ zeroProfileHistogram := by
  simp [ProfileAdmissible]

/-- The template cardinality for the zero histogram is the singleton count. -/
theorem profileTemplateBound_zeroProfileHistogram :
    profileTemplateBound zeroProfileHistogram = 1 := by
  classical
  simp [profileTemplateBound, zeroProfileHistogram]

/-- If a derivative-count profile is zero, every factor receives zero
derivatives. -/
theorem derivCountProfile_eq_zeroProfile_length_eq_zero {n L : ℕ}
    (constraintType : Fin L → ConstraintType)
    (d : Fin L → List (Fin n))
    (hprof : derivCountProfile constraintType d = zeroProfileHistogram) :
    ∀ i : Fin L, (d i).length = 0 := by
  have hsum : (∑ i : Fin L, (d i).length) = 0 := by
    calc
      (∑ i : Fin L, (d i).length)
          = profileMass (derivCountProfile constraintType d) :=
            (derivCountProfile_mass constraintType d).symm
      _ = profileMass zeroProfileHistogram := by rw [hprof]
      _ = 0 := profileMass_zeroProfileHistogram
  intro i
  have hle : (d i).length ≤ ∑ j : Fin L, (d j).length :=
    Finset.single_le_sum
      (f := fun j : Fin L => (d j).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [hsum] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- If a derivative-count profile is zero, every factor receives the empty
derivative list. -/
theorem derivCountProfile_eq_zeroProfile_eq_nil {n L : ℕ}
    (constraintType : Fin L → ConstraintType)
    (d : Fin L → List (Fin n))
    (hprof : derivCountProfile constraintType d = zeroProfileHistogram) :
    ∀ i : Fin L, d i = [] := by
  intro i
  have hlen :=
    derivCountProfile_eq_zeroProfile_length_eq_zero constraintType d hprof i
  cases hdi : d i with
  | nil => rfl
  | cons _ _ =>
      simp [hdi] at hlen

/-- For the zero profile, the bounded classified set is exactly the singleton
base product.  This is independent of the list `S`: any nonempty derivative
assignment would create positive profile mass. -/
theorem boundedProfileClassifiedSet_zeroProfile_eq_singleton {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n)) :
    boundedProfileClassifiedSet factors constraintType S zeroProfileHistogram =
      ({Finset.univ.prod factors} : Set (MvPolynomial (Fin n) ℚ)) := by
  ext g
  constructor
  · intro hg
    rcases hg with ⟨d, _hd_elts, hg_eq, hprof, _hlen⟩
    have hd_nil := derivCountProfile_eq_zeroProfile_eq_nil constraintType d hprof
    rw [hg_eq]
    congr 1
    funext i
    simp [hd_nil i]
  · intro hg
    have hg_eq : g = Finset.univ.prod factors := by
      simpa using hg
    subst g
    refine ⟨fun _ => [], ?_, ?_, ?_, ?_⟩
    · intro _ v hv
      cases hv
    · simp
    · funext τ
      simp [derivCountProfile, zeroProfileHistogram]
    · simp

/-- Per-`S`/shift zero-profile post-span: after classification, it is generated
by the single shifted base product. -/
theorem boundedProfilePostSpan_zeroProfile_eq_singleton_span {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin n))
    (shift : MvPolynomial (Fin n) ℚ) :
    boundedProfilePostSpan factors constraintType S shift zeroProfileHistogram =
      Submodule.span ℚ
        ({mlProj (shift * Finset.univ.prod factors)} :
          Set (MvPolynomial (Fin n) ℚ)) := by
  simp [boundedProfilePostSpan,
    boundedProfileClassifiedSet_zeroProfile_eq_singleton factors constraintType S]

/-- The shifted base-product family that remains after reducing the zero
histogram classification. -/
noncomputable def zeroProfileShiftImageSet {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ) :
    Set (MvPolynomial (Fin n) ℚ) :=
  ⋃ (S : List (Fin n)) (_ : S.length ≤ κ)
      (shift : MvPolynomial (Fin n) ℚ) (_ : shift.vars ⊆ S.toFinset),
    ({mlProj (shift * Finset.univ.prod factors)} :
      Set (MvPolynomial (Fin n) ℚ))

/-- The full all-`S`/shift zero-profile span is exactly the span of the shifted
base-product family. -/
theorem allBoundedProfilePostSpan_zeroProfile_eq_shiftImageSpan {n L : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (constraintType : Fin L → ConstraintType) :
    allBoundedProfilePostSpan B κ ℓ factors constraintType zeroProfileHistogram =
      Submodule.span ℚ (zeroProfileShiftImageSet κ factors) := by
  simp [allBoundedProfilePostSpan, zeroProfileShiftImageSet,
    boundedProfileClassifiedSet_zeroProfile_eq_singleton factors constraintType]

/-- Exact remaining all-span blocker for the Cook-Levin all-zero profile:
one finite family, of the `withinProfileBound` size, must span the shifted
base-product image. -/
def CookLevinZeroHistogramShiftCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ G : Finset (MvPolynomial (Fin n) ℚ),
    G.card ≤ withinProfileBound (Nat.log 2 n) ∧
    zeroProfileShiftImageSet (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
      ⊆ Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))

/-- The exact shifted-base-product blocker is sufficient for the requested
all-bounded common-span target at the admissible all-zero histogram. -/
theorem cookLevinAllBoundedProfileCommonSpanAtProfile_zero_of_shiftCommonSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hspan : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns) :
    CookLevinAllBoundedProfileCommonSpanAtProfile
      M n hn htb hns zeroProfileHistogram := by
  rcases hspan with ⟨G, hG_card, hG_span⟩
  refine ⟨G, hG_card, ?_⟩
  rw [allBoundedProfilePostSpan_zeroProfile_eq_shiftImageSpan
    (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (cookLevinConstraintType M n hn htb hns)]
  exact Submodule.span_le.mpr hG_span

/-- Sharper template version of the same zero-profile shift blocker.  Since
`profileTemplateBound zeroProfileHistogram = 1`, this asks for a singleton
template span for the shifted base-product family. -/
def CookLevinZeroHistogramTemplateShiftCollapse
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ G : Finset (MvPolynomial (Fin n) ℚ),
    G.card ≤ profileTemplateBound zeroProfileHistogram ∧
    zeroProfileShiftImageSet (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
      ⊆ Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))

/-- The sharper shifted-base-product blocker is sufficient for the requested
template-collapse target at the admissible all-zero histogram. -/
theorem cookLevinProfileTemplateCollapseAtProfile_zero_of_templateShiftCollapse
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hspan : CookLevinZeroHistogramTemplateShiftCollapse M n hn htb hns) :
    CookLevinProfileTemplateCollapseAtProfile
      M n hn htb hns zeroProfileHistogram := by
  rcases hspan with ⟨G, hG_card, hG_span⟩
  refine ⟨G, ?_, hG_card⟩
  rw [allBoundedProfilePostSpan_zeroProfile_eq_shiftImageSpan
    (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (cookLevinConstraintType M n hn htb hns)]
  exact Submodule.span_le.mpr hG_span

/-! ## Axiom audit anchors -/

#print axioms boundedProfileClassifiedSet_zeroProfile_eq_singleton
#print axioms allBoundedProfilePostSpan_zeroProfile_eq_shiftImageSpan
#print axioms cookLevinAllBoundedProfileCommonSpanAtProfile_zero_of_shiftCommonSpan
#print axioms cookLevinProfileTemplateCollapseAtProfile_zero_of_templateShiftCollapse

end PathB
end DeepMath
end Paper93
end PallLean
