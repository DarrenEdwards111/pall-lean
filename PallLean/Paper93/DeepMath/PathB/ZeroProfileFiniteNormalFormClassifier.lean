import PallLean.Paper93.DeepMath.PathB.ZeroProfileNormalFormInstantiationProgress
import PallLean.Paper93.ShortlexNormalForm

/-!
# Zero-profile finite normal-form classifier

This file gives the zero-profile compression target the paper's local
normal-form vocabulary.

The existing `ZeroProfileProjectedNormalFormRowMap` is the right downstream
object, but it does not remember why its index type is a finite local
normal-form alphabet.  The structures below add that source data:

* a finite local normal-form alphabet, optionally obtained from a finite local
  monoid by the shortlex `NF` construction from paper §9.3;
* a classifier from projected zero-profile rows into that alphabet;
* constructors turning such a classifier into the existing projected
  normal-form row map, and then into the singleton-quotient projected budget.

No row factorization is asserted for free: the classifier still has to prove
that every projected row lands in the selected normal-form/profile span.
-/

namespace PallLean
namespace Paper93
namespace DeepMath
namespace PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP SPDP
open scoped BigOperators

attribute [local instance] Classical.dec

/-! ## Finite local normal-form alphabets -/

/-- A finite local normal-form alphabet for the zero-profile classifier.

The alphabet is intentionally separate from the global row family: it records
the paper's `Σ^{≤q}` / finite-monoid normal forms, while the row classifier
below records how actual projected rows factor through it. -/
structure ZeroProfileFiniteNormalFormAlphabet (κ : ℕ) where
  normalForm : Type
  [normalFormFintype : Fintype normalForm]
  profile : normalForm → ProfileHistogram
  profile_admissible : ∀ ν, ProfileAdmissible κ (profile ν)

attribute [instance] ZeroProfileFiniteNormalFormAlphabet.normalFormFintype

/-- A finite local monoid presentation of a normal-form alphabet.  This is the
paper §9.3 `NF` route: each monoid element has a bounded shortlex
representative word over the fixed local generators. -/
structure ZeroProfileFiniteLocalMonoid where
  localMonoid : Type
  [localMonoidMonoid : Monoid localMonoid]
  [localMonoidFintype : Fintype localMonoid]
  [localMonoidDecidableEq : DecidableEq localMonoid]
  generators : List localMonoid

attribute [instance] ZeroProfileFiniteLocalMonoid.localMonoidMonoid
attribute [instance] ZeroProfileFiniteLocalMonoid.localMonoidFintype
attribute [instance] ZeroProfileFiniteLocalMonoid.localMonoidDecidableEq

namespace ZeroProfileFiniteLocalMonoid

/-- The shortlex local normal form of a monoid element. -/
noncomputable def normalFormWord (A : ZeroProfileFiniteLocalMonoid)
    (g : A.localMonoid) : List A.localMonoid :=
  PallLean.Paper93.NF A.generators g

/-- Paper §9.3 Lemma 25 length bound, specialized to a local monoid
presentation. -/
theorem normalFormWord_length_bound (A : ZeroProfileFiniteLocalMonoid) :
    ∃ q, ∀ g : A.localMonoid, (A.normalFormWord g).length ≤ q :=
  PallLean.Paper93.NF_length_bound A.generators

/-- Paper §9.3 Lemma 25 representation property, specialized to a local
monoid presentation. -/
theorem normalFormWord_represents (A : ZeroProfileFiniteLocalMonoid)
    (g : A.localMonoid) :
    (A.normalFormWord g).prod = g :=
  PallLean.Paper93.NF_represents A.generators g

end ZeroProfileFiniteLocalMonoid

/-- Turn a finite local monoid into a finite normal-form alphabet by using
monoid elements as the normal forms and supplying the profile interpretation
separately. -/
def ZeroProfileFiniteNormalFormAlphabet.ofLocalMonoid
    (κ : ℕ) (A : ZeroProfileFiniteLocalMonoid)
    (profile : A.localMonoid → ProfileHistogram)
    (profile_admissible : ∀ g, ProfileAdmissible κ (profile g)) :
    ZeroProfileFiniteNormalFormAlphabet κ where
  normalForm := A.localMonoid
  normalFormFintype := inferInstance
  profile := profile
  profile_admissible := profile_admissible

/-! ## Family data and row classifiers -/

/-- Local spanning data attached to each finite normal form.

This is the symmetric-power/profile span side of paper §9.1/§9.3: each normal
form has a profile histogram and a local basis whose size is bounded by the
corresponding symmetric-profile dimension. -/
structure ZeroProfileFiniteNormalFormFamilyData
    {κ : ℕ} (A : ZeroProfileFiniteNormalFormAlphabet κ)
    (n typeBudget : ℕ) where
  localBasis : A.normalForm → Finset (MvPolynomial (Fin n) ℚ)
  localBasis_card_le_profileDim :
    ∀ ν, (localBasis ν).card ≤ zeroProfileSymmetricProfileDim (A.profile ν)
  totalProfileBudget_le :
    (∑ ν : A.normalForm, zeroProfileSymmetricProfileDim (A.profile ν)) ≤
      typeBudget

/-- Forget the normal-form source data and build the downstream projected
normal-form family already consumed by the zero-profile quotient bridge. -/
noncomputable def ZeroProfileFiniteNormalFormFamilyData.toProjectedFamily
    {κ n typeBudget : ℕ}
    {A : ZeroProfileFiniteNormalFormAlphabet κ}
    (D : ZeroProfileFiniteNormalFormFamilyData A n typeBudget) :
    ZeroProfileProjectedNormalFormFamily n κ typeBudget where
  normalForm := A.normalForm
  normalFormFintype := inferInstance
  profile := A.profile
  profile_admissible := A.profile_admissible
  localBasis := D.localBasis
  localBasis_card_le_profileDim := D.localBasis_card_le_profileDim
  totalProfileBudget_le := D.totalProfileBudget_le

/-- A projected zero-profile row classifier into a finite local normal-form
alphabet.  This is the concrete factor-through proof still owed by the
Cook-Levin local chart family. -/
structure ZeroProfileFiniteNormalFormRowClassifier
    {n L κ typeBudget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    {A : ZeroProfileFiniteNormalFormAlphabet κ}
    (D : ZeroProfileFiniteNormalFormFamilyData A n typeBudget) where
  rowNormalForm :
    ∀ (S : List (Fin n)), S.length ≤ κ →
      ∀ shift : MvPolynomial (Fin n) ℚ, shift.vars ⊆ S.toFinset →
        A.normalForm
  projected_row_mem_normalFormSpace :
    ∀ (S : List (Fin n)) (hS : S.length ≤ κ)
      (shift : MvPolynomial (Fin n) ℚ) (hshift : shift.vars ⊆ S.toFinset),
        project (mlProj (shift * Finset.univ.prod factors)) ∈
          zeroProfileProjectedNormalFormSpace D.toProjectedFamily
            (rowNormalForm S hS shift hshift)

/-- A finite-normal-form classifier is exactly the existing projected
normal-form row map after forgetting its local alphabet origin. -/
def ZeroProfileFiniteNormalFormRowClassifier.toRowMap
    {n L κ typeBudget : ℕ}
    {factors : Fin L → MvPolynomial (Fin n) ℚ}
    {project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ}
    {A : ZeroProfileFiniteNormalFormAlphabet κ}
    {D : ZeroProfileFiniteNormalFormFamilyData A n typeBudget}
    (C : ZeroProfileFiniteNormalFormRowClassifier factors project D) :
    ZeroProfileProjectedNormalFormRowMap factors project D.toProjectedFamily where
  rowNormalForm := C.rowNormalForm
  projected_row_mem_normalFormSpace :=
    C.projected_row_mem_normalFormSpace

/-- The finite-normal-form classifier closes the projected common-span target. -/
theorem zeroProfileProjectedCommonSpanWithBudget_of_finiteNormalFormClassifier
    {n L κ typeBudget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    {A : ZeroProfileFiniteNormalFormAlphabet κ}
    (D : ZeroProfileFiniteNormalFormFamilyData A n typeBudget)
    (C : ZeroProfileFiniteNormalFormRowClassifier factors project D) :
    ZeroProfileProjectedCommonSpanWithBudget
      κ factors project typeBudget :=
  zeroProfileProjectedCommonSpanWithBudget_of_normalFormRowMap
    factors project D.toProjectedFamily C.toRowMap

/-- Core finrank consequence of a budgeted projected common span.

This duplicate is kept in `PathB`, rather than importing the Route B assembly
module, so the local classifier remains usable by lower-level zero-profile
code. -/
theorem zeroProfileProjectedShiftSpan_finrank_le_of_commonSpanWithBudget_core
    {n L κ budget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hspan :
      ZeroProfileProjectedCommonSpanWithBudget κ factors project budget) :
    Module.finrank ℚ ↥(zeroProfileProjectedShiftSpan κ factors project) ≤
      budget := by
  classical
  rcases hspan with ⟨G, hG_card, hG_span⟩
  have hle :
      zeroProfileProjectedShiftSpan κ factors project ≤
        Submodule.span ℚ
          (↑G : Set (MvPolynomial (Fin n) ℚ)) := by
    rw [zeroProfileProjectedShiftSpan_eq_span_projectedShiftImageSet]
    exact Submodule.span_le.mpr hG_span
  haveI hprojFinite :
      Module.Finite ℚ ↥(zeroProfileProjectedShiftSpan κ factors project) :=
    zeroProfileProjectedShiftSpan_finite κ factors project
  haveI hspanFinite :
      Module.Finite ℚ
        ↥(Submodule.span ℚ
          (↑G : Set (MvPolynomial (Fin n) ℚ))) :=
    Module.Finite.span_of_finite ℚ (Finset.finite_toSet G)
  exact
    (Submodule.finrank_mono hle).trans
      ((finrank_span_finset_le_card G).trans hG_card)

/-! ## Cook-Levin singleton-quotient budget from a finite classifier -/

/-- A finite normal-form classifier for the singleton quotient closes the
quotiented zero-profile target when its symmetric-profile budget fits inside
`withinProfileBound`. -/
theorem cookLevinZeroProfileQuotientedShiftCommonSpan_of_finiteNormalFormClassifier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget : ℕ}
    {A : ZeroProfileFiniteNormalFormAlphabet (Nat.log 2 n)}
    (D : ZeroProfileFiniteNormalFormFamilyData A n typeBudget)
    (C :
      ZeroProfileFiniteNormalFormRowClassifier
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn htb hns).get i))
        D)
    (hbudget : typeBudget ≤ withinProfileBound (Nat.log 2 n)) :
    CookLevinZeroProfileQuotientedShiftCommonSpan
      M n hn htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn htb hns).get i)) :=
  cookLevinZeroProfileQuotientedShiftCommonSpan_of_singletonQuotientNormalFormRowMap
    M n hn htb hns D.toProjectedFamily C.toRowMap hbudget

/-- The same finite normal-form classifier proves the exact projected
singleton-quotient type-budget inequality.  This is the current zero-profile
gate in its paper-faithful classifier form. -/
theorem zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_finiteNormalFormClassifier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget : ℕ}
    {A : ZeroProfileFiniteNormalFormAlphabet (Nat.log 2 n)}
    (D : ZeroProfileFiniteNormalFormFamilyData A n typeBudget)
    (C :
      ZeroProfileFiniteNormalFormRowClassifier
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn htb hns).get i))
        D)
    (hbudget : typeBudget ≤ withinProfileBound (Nat.log 2 n)) :
    zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i) ≤
      withinProfileBound (Nat.log 2 n) := by
  have hquot :
      CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn htb hns).get i)) :=
    cookLevinZeroProfileQuotientedShiftCommonSpan_of_finiteNormalFormClassifier
      M n hn htb hns D C hbudget
  simpa [zeroProfileSingletonQuotientProjectedTypeBudget] using
    zeroProfileProjectedShiftSpan_finrank_le_of_commonSpanWithBudget_core
      (κ := Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn htb hns).get i))
      hquot.2.2

/-! ## Axiom audit anchors -/

#print axioms ZeroProfileFiniteLocalMonoid.normalFormWord_length_bound
#print axioms ZeroProfileFiniteLocalMonoid.normalFormWord_represents
#print axioms zeroProfileProjectedCommonSpanWithBudget_of_finiteNormalFormClassifier
#print axioms zeroProfileProjectedShiftSpan_finrank_le_of_commonSpanWithBudget_core
#print axioms cookLevinZeroProfileQuotientedShiftCommonSpan_of_finiteNormalFormClassifier
#print axioms zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_finiteNormalFormClassifier

end PathB
end DeepMath
end Paper93
end PallLean
