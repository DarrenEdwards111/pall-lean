import PallLean.Paper93.DeepMath.PathB.ZeroProfileNormalFormInstantiationProgress
import PallLean.Paper93.DeepMath.PathB.ZeroProfileFiniteNormalFormClassifier
import PallLean.Paper93.CompiledCoefficientBasis
import PallLean.Paper93.Direct.PerTypeComposition
import PallLean.Paper93.TensorDimBound
import PallLean.Paper93.Wiring.ConcreteW

/-!
# Concrete zero-profile normal-form progress

This file instantiates the projected zero-profile normal-form interface with
the concrete finite profile/symmetric-power objects already present in the
repository.

The important point is negative as well as positive: the in-tree data contains
`ConstraintType`, `ProfileHistogram`, `BoundedProfile`, `ProfileIndex`, and the
finite symmetric basis products `profileSymProd`, but it does not yet contain a
Cook-Levin local monoid normal-form classifier for projected zero-profile rows.
Accordingly, this file proves the exact bridge from such a classifier to the
existing Route B zero-profile certificate, without falling back to raw
shift-support counting.
-/

namespace PallLean
namespace Paper93
namespace DeepMath
namespace PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP SPDP
open scoped BigOperators

attribute [local instance] Classical.dec

/-! ## Existing finite profile alphabet -/

/-- Admissible bounded profiles are the finite in-repo replacement for ranging
over all histograms.  The `BoundedProfile` wrapper supplies finiteness; the
subtype predicate keeps only the paper-relevant `profileMass ≤ κ` profiles. -/
abbrev ZeroProfileAdmissibleBoundedProfile (κ : ℕ) : Type :=
  { bp : BoundedProfile κ // ProfileAdmissible κ bp.toHistogram }

namespace ZeroProfileAdmissibleBoundedProfile

/-- The histogram represented by an admissible bounded profile. -/
def toHistogram {κ : ℕ} (bp : ZeroProfileAdmissibleBoundedProfile κ) :
    ProfileHistogram :=
  bp.val.toHistogram

/-- The represented histogram is admissible. -/
theorem admissible {κ : ℕ} (bp : ZeroProfileAdmissibleBoundedProfile κ) :
    ProfileAdmissible κ bp.toHistogram :=
  bp.property

@[simp] theorem val_toHistogram {κ : ℕ}
    (bp : ZeroProfileAdmissibleBoundedProfile κ) :
    bp.val.toHistogram = bp.toHistogram :=
  rfl

end ZeroProfileAdmissibleBoundedProfile

/-! ## Concrete symmetric-power chart for one normal form -/

/-- A concrete local chart for one zero-profile normal form.

For the chosen profile `h`, each constraint type has a local chart `W τ` with a
basis indexed by `Fin (d τ)`, and every `d τ` is at most the paper constant
three.  This is exactly the data needed by `profileSymProd`; it avoids a fake
shared `W_τ` proof in the uniform polynomial basis by making the chart data an
explicit obligation. -/
structure ZeroProfileConcreteLocalChart (n : ℕ) (h : ProfileHistogram) where
  d : ConstraintType → ℕ
  d_le_three : ∀ τ, d τ ≤ 3
  W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)
  basis : ∀ τ, Module.Basis (Fin (d τ)) ℚ ↥(W τ)

/-- Package any finite three-dimensional per-type family as a concrete local
chart.  This is used below both for the compiled coefficient-basis chart and
for the existing `concreteW` row-embedding family. -/
noncomputable def zeroProfileConcreteLocalChart_of_submoduleFamily
    {n : ℕ} (h : ProfileHistogram)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hfinite : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hdim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3) :
    ZeroProfileConcreteLocalChart n h where
  d := fun τ => Module.finrank ℚ ↥(W τ)
  d_le_three := hdim
  W := W
  basis := fun τ => by
    letI : Module.Finite ℚ ↥(W τ) := hfinite τ
    exact Module.finBasis ℚ ↥(W τ)

/-- The compiled coefficient-basis local chart from paper §9 Lemma 31,
packaged as the zero-profile concrete chart.  The local spaces are the
in-repo `interfaceSpace_compiledBasis`, whose finrank is already proved to be
at most three uniformly in the interface type. -/
noncomputable def zeroProfileConcreteLocalChart_compiledCoefficientBasis
    {n : ℕ} (B : SPDP.BlockPartition n) (κ ℓ : ℕ)
    (h : ProfileHistogram) :
    ZeroProfileConcreteLocalChart n h :=
  zeroProfileConcreteLocalChart_of_submoduleFamily h
    (fun τ => PallLean.Paper93.interfaceSpace_compiledBasis B κ ℓ τ)
    (fun τ => PallLean.Paper93.interfaceSpace_compiledBasis_finite B κ ℓ τ)
    (fun τ =>
      PallLean.Paper93.interfaceSpace_compiledBasis_finrank_le_three
        B κ ℓ τ)

/-- The existing `concreteW` family as a zero-profile concrete chart. -/
noncomputable def zeroProfileConcreteLocalChart_concreteW
    {n : ℕ} (hn4 : n ≥ 4) (h : ProfileHistogram) :
    ZeroProfileConcreteLocalChart n h :=
  zeroProfileConcreteLocalChart_of_submoduleFamily h
    (fun τ =>
      PallLean.Paper93.Wiring.concreteW n hn4 (Fin.castLEEmb hn4) τ)
    (fun τ =>
      PallLean.Paper93.Wiring.concreteW_finite
        n hn4 (Fin.castLEEmb hn4) τ)
    (fun τ =>
      PallLean.Paper93.Wiring.concreteW_finrank_le_three
        n hn4 (Fin.castLEEmb hn4) τ)

/-- The finite symmetric-power basis products for one concrete local chart. -/
noncomputable def zeroProfileConcreteNormalFormBasis
    {n : ℕ} {h : ProfileHistogram}
    (C : ZeroProfileConcreteLocalChart n h) :
    Finset (MvPolynomial (Fin n) ℚ) :=
  (Finset.univ : Finset (ProfileIndex h C.d)).image
    (profileSymProd C.W C.basis)

/-- The concrete normal-form basis has the expected symmetric-power cardinality
bound for its profile. -/
theorem zeroProfileConcreteNormalFormBasis_card_le_profileDim
    {n : ℕ} {h : ProfileHistogram}
    (C : ZeroProfileConcreteLocalChart n h) :
    (zeroProfileConcreteNormalFormBasis C).card ≤
      zeroProfileSymmetricProfileDim h := by
  classical
  have himage :
      (zeroProfileConcreteNormalFormBasis C).card ≤
        Fintype.card (ProfileIndex h C.d) := by
    unfold zeroProfileConcreteNormalFormBasis
    calc
      ((Finset.univ : Finset (ProfileIndex h C.d)).image
          (profileSymProd C.W C.basis)).card
          ≤ (Finset.univ : Finset (ProfileIndex h C.d)).card :=
            Finset.card_image_le
      _ = Fintype.card (ProfileIndex h C.d) := Finset.card_univ
  have hcard :
      Fintype.card (ProfileIndex h C.d) =
        ∏ τ : ConstraintType, Nat.multichoose (C.d τ) (h τ) :=
    profileIndex_card h C.d
  have hfac :
      (∏ τ : ConstraintType, Nat.multichoose (C.d τ) (h τ)) ≤
        ∏ τ : ConstraintType, Nat.choose (h τ + 2) 2 := by
    exact Finset.prod_le_prod
      (by intro τ _hτ; exact Nat.zero_le _)
      (by
        intro τ _hτ
        exact multichoose_le_choose_of_dim_le_three
          (C.d τ) (h τ) (C.d_le_three τ))
  calc
    (zeroProfileConcreteNormalFormBasis C).card
        ≤ Fintype.card (ProfileIndex h C.d) := himage
    _ = ∏ τ : ConstraintType, Nat.multichoose (C.d τ) (h τ) := hcard
    _ ≤ ∏ τ : ConstraintType, Nat.choose (h τ + 2) 2 := hfac
    _ = zeroProfileSymmetricProfileDim h := by
      rfl

/-- The profile subspace represented by a concrete chart is contained in the
span of the finite symmetric-power basis products above. -/
theorem profileSubspace_le_zeroProfileConcreteNormalFormBasis_span
    {n : ℕ} {h : ProfileHistogram}
    (C : ZeroProfileConcreteLocalChart n h) :
    profileSubspace h C.W ≤
      Submodule.span ℚ
        (↑(zeroProfileConcreteNormalFormBasis C) :
          Set (MvPolynomial (Fin n) ℚ)) := by
  classical
  refine le_trans (profileSubspace_le_profileSymProd_span C.W C.basis) ?_
  apply Submodule.span_mono
  intro q hq
  rcases hq with ⟨m, rfl⟩
  change profileSymProd C.W C.basis m ∈ zeroProfileConcreteNormalFormBasis C
  unfold zeroProfileConcreteNormalFormBasis
  exact Finset.mem_image.mpr ⟨m, Finset.mem_univ m, rfl⟩

/-! ## Concrete normal-form data and bridge to the existing interface -/

/-- Concrete projected zero-profile normal-form data.

The finite type `normalForm` is now not an opaque row-support set: every normal
form carries a profile histogram and a concrete symmetric-power chart. -/
structure ZeroProfileConcreteNormalFormData
    (n κ typeBudget : ℕ) where
  normalForm : Type
  [normalFormFintype : Fintype normalForm]
  profile : normalForm → ProfileHistogram
  profile_admissible : ∀ ν, ProfileAdmissible κ (profile ν)
  chart : ∀ ν, ZeroProfileConcreteLocalChart n (profile ν)
  totalProfileBudget_le :
    (∑ ν : normalForm, zeroProfileSymmetricProfileDim (profile ν)) ≤
      typeBudget

/-- The symmetric-power dimension of the all-zero profile is one. -/
theorem zeroProfileSymmetricProfileDim_zeroProfileHistogram :
    zeroProfileSymmetricProfileDim zeroProfileHistogram = 1 := by
  classical
  simp [zeroProfileSymmetricProfileDim, zeroProfileHistogram]

/-- Singleton normal-form data for the all-zero profile over any concrete
three-dimensional local chart.  This is the smallest genuine
symmetric-power/profile alphabet: one normal form, carrying the all-zero
histogram, with budget one. -/
noncomputable def zeroProfileConcreteNormalFormData_singletonZeroProfile
    {n κ : ℕ}
    (C : ZeroProfileConcreteLocalChart n zeroProfileHistogram) :
    ZeroProfileConcreteNormalFormData n κ
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) where
  normalForm := PUnit
  normalFormFintype := inferInstance
  profile := fun _ => zeroProfileHistogram
  profile_admissible := fun _ => zeroProfileHistogram_admissible κ
  chart := fun _ => C
  totalProfileBudget_le := by
    simp

/-- Singleton zero-profile concrete normal-form data for `concreteW`. -/
noncomputable def zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
    {n κ : ℕ} (hn4 : n ≥ 4) :
    ZeroProfileConcreteNormalFormData n κ
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) :=
  zeroProfileConcreteNormalFormData_singletonZeroProfile
    (zeroProfileConcreteLocalChart_concreteW hn4 zeroProfileHistogram)

/-- The concrete data as a `ZeroProfileProjectedNormalFormFamily`. -/
noncomputable def zeroProfileProjectedNormalFormFamily_of_concreteData
    {n κ typeBudget : ℕ}
    (D : ZeroProfileConcreteNormalFormData n κ typeBudget) :
    ZeroProfileProjectedNormalFormFamily n κ typeBudget where
  normalForm := D.normalForm
  normalFormFintype := D.normalFormFintype
  profile := D.profile
  profile_admissible := D.profile_admissible
  localBasis := fun ν => zeroProfileConcreteNormalFormBasis (D.chart ν)
  localBasis_card_le_profileDim := fun ν =>
    zeroProfileConcreteNormalFormBasis_card_le_profileDim (D.chart ν)
  totalProfileBudget_le := D.totalProfileBudget_le

/-! ## Bridge to finite local normal-form classifiers -/

/-- The concrete symmetric-power chart data carries the finite normal-form
alphabet required by the classifier route. -/
noncomputable def zeroProfileFiniteNormalFormAlphabet_of_concreteData
    {n κ typeBudget : ℕ}
    (D : ZeroProfileConcreteNormalFormData n κ typeBudget) :
    ZeroProfileFiniteNormalFormAlphabet κ where
  normalForm := D.normalForm
  normalFormFintype := D.normalFormFintype
  profile := D.profile
  profile_admissible := D.profile_admissible

/-- The same concrete symmetric-power bases instantiate the finite
normal-form family data. -/
noncomputable def zeroProfileFiniteNormalFormFamilyData_of_concreteData
    {n κ typeBudget : ℕ}
    (D : ZeroProfileConcreteNormalFormData n κ typeBudget) :
    ZeroProfileFiniteNormalFormFamilyData
      (zeroProfileFiniteNormalFormAlphabet_of_concreteData D)
      n typeBudget where
  localBasis := fun ν => zeroProfileConcreteNormalFormBasis (D.chart ν)
  localBasis_card_le_profileDim := fun ν =>
    zeroProfileConcreteNormalFormBasis_card_le_profileDim (D.chart ν)
  totalProfileBudget_le := D.totalProfileBudget_le

/-- Concrete charts for the finite admissible-profile alphabet already present
in the repository. -/
structure ZeroProfileAdmissibleProfileChartFamily
    (n κ typeBudget : ℕ) where
  chart :
    ∀ bp : ZeroProfileAdmissibleBoundedProfile κ,
      ZeroProfileConcreteLocalChart n bp.toHistogram
  totalProfileBudget_le :
    (∑ bp : ZeroProfileAdmissibleBoundedProfile κ,
        zeroProfileSymmetricProfileDim bp.toHistogram) ≤ typeBudget

/-- The compiled coefficient-basis chart family over all admissible bounded
profiles.  The remaining arithmetic input is the global profile/type budget
for the chosen finite profile alphabet. -/
noncomputable def zeroProfileAdmissibleProfileChartFamily_compiledCoefficientBasis
    {n κ typeBudget : ℕ}
    (B : SPDP.BlockPartition n) (ℓ : ℕ)
    (hbudget :
      (∑ bp : ZeroProfileAdmissibleBoundedProfile κ,
          zeroProfileSymmetricProfileDim bp.toHistogram) ≤ typeBudget) :
    ZeroProfileAdmissibleProfileChartFamily n κ typeBudget where
  chart := fun bp =>
    zeroProfileConcreteLocalChart_compiledCoefficientBasis
      B κ ℓ bp.toHistogram
  totalProfileBudget_le := hbudget

/-- The in-repo finite admissible-profile alphabet as concrete normal-form
data.  This is the most concrete alphabet available without adding the missing
local monoid classifier. -/
noncomputable def zeroProfileConcreteNormalFormData_of_admissibleProfileCharts
    {n κ typeBudget : ℕ}
    (C : ZeroProfileAdmissibleProfileChartFamily n κ typeBudget) :
    ZeroProfileConcreteNormalFormData n κ typeBudget where
  normalForm := ZeroProfileAdmissibleBoundedProfile κ
  normalFormFintype := inferInstance
  profile := fun bp => bp.toHistogram
  profile_admissible := fun bp => bp.admissible
  chart := C.chart
  totalProfileBudget_le := C.totalProfileBudget_le

/-- Row typing through the concrete symmetric-power chart.

This is the exact missing Cook-Levin row-map proof: after projection, each
zero-profile shifted row must choose a finite normal form and land in that
normal form's concrete profile subspace. -/
structure ZeroProfileConcreteNormalFormRowMap {n L κ typeBudget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (D : ZeroProfileConcreteNormalFormData n κ typeBudget) where
  rowNormalForm :
    ∀ (S : List (Fin n)), S.length ≤ κ →
      ∀ shift : MvPolynomial (Fin n) ℚ, shift.vars ⊆ S.toFinset →
        D.normalForm
  projected_row_mem_profileSubspace :
    ∀ (S : List (Fin n)) (hS : S.length ≤ κ)
      (shift : MvPolynomial (Fin n) ℚ) (hshift : shift.vars ⊆ S.toFinset),
        project (mlProj (shift * Finset.univ.prod factors)) ∈
          profileSubspace
            (D.profile (rowNormalForm S hS shift hshift))
            (D.chart (rowNormalForm S hS shift hshift)).W

/-- Actual zero-profile row classifier obtained from the direct `concreteW`
row-embedding package.

This is the concrete factor-through proof for the all-zero profile under the
existing per-type row-embedding bundle: reducing
`allBoundedProfilePostSpan` at the zero histogram identifies the generators
with the shifted base-product rows, and the direct `concreteW` containment
places those rows in the zero-profile symmetric-power subspace. -/
noncomputable def zeroProfileConcreteNormalFormRowMap_id_concreteW_of_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    ZeroProfileConcreteNormalFormRowMap
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (LinearMap.id :
        MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
      (zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
        (κ := Nat.log 2 n) hn4) where
  rowNormalForm := fun _ _ _ _ => PUnit.unit
  projected_row_mem_profileSubspace := by
    intro S hS shift hshift
    let factors : Fin (cookLevinFactorList M n hn htb hns).length →
        MvPolynomial (Fin n) ℚ :=
      fun i => (cookLevinFactorList M n hn htb hns).get i
    let W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
      fun τ =>
        PallLean.Paper93.Wiring.concreteW
          n hn4 (Fin.castLEEmb hn4) τ
    let bp : BoundedProfile (Nat.log 2 n) :=
      admissibleToBounded (zeroProfileHistogram_admissible (Nat.log 2 n))
    have hpost :
        allBoundedProfilePostSpan
            (PaperFaithfulSeparation.cook_levin_compilation
              M n hn htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            factors
            (cookLevinConstraintType M n hn htb hns)
            zeroProfileHistogram
          ≤ cookLevinProfileSubspace bp W := by
      simpa [bp, W, factors, cookLevinPostSpanAt] using
        PallLean.Paper93.Direct.cookLevinProfileSubspace_contains_postSpan_direct
          M n hn htb hns hn4 bp hRowEmbeddings
    have hrowSet :
        mlProj (shift * Finset.univ.prod factors) ∈
          zeroProfileShiftImageSet (Nat.log 2 n) factors := by
      simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
        Set.mem_singleton_iff]
      exact ⟨S, hS, shift, hshift, rfl⟩
    have hrowPost :
        mlProj (shift * Finset.univ.prod factors) ∈
          allBoundedProfilePostSpan
            (PaperFaithfulSeparation.cook_levin_compilation
              M n hn htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            factors
            (cookLevinConstraintType M n hn htb hns)
            zeroProfileHistogram := by
      rw [allBoundedProfilePostSpan_zeroProfile_eq_shiftImageSpan
        (PaperFaithfulSeparation.cook_levin_compilation
          M n hn htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n)
        factors
        (cookLevinConstraintType M n hn htb hns)]
      exact Submodule.subset_span hrowSet
    have hmem :
        mlProj (shift * Finset.univ.prod factors) ∈
          cookLevinProfileSubspace bp W :=
      hpost hrowPost
    simpa [LinearMap.id_apply, bp, W, factors,
      cookLevinProfileSubspace,
      zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW,
      zeroProfileConcreteNormalFormData_singletonZeroProfile,
      zeroProfileConcreteLocalChart_concreteW,
      zeroProfileConcreteLocalChart_of_submoduleFamily] using hmem

/-- A concrete row map gives the existing projected normal-form row map. -/
noncomputable def zeroProfileProjectedNormalFormRowMap_of_concreteRowMap
    {n L κ typeBudget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (D : ZeroProfileConcreteNormalFormData n κ typeBudget)
    (hmap : ZeroProfileConcreteNormalFormRowMap factors project D) :
    ZeroProfileProjectedNormalFormRowMap factors project
      (zeroProfileProjectedNormalFormFamily_of_concreteData D) where
  rowNormalForm := hmap.rowNormalForm
  projected_row_mem_normalFormSpace := by
    intro S hS shift hshift
    let ν := hmap.rowNormalForm S hS shift hshift
    have hrow :
        project (mlProj (shift * Finset.univ.prod factors)) ∈
          profileSubspace (D.profile ν) (D.chart ν).W := by
      simpa [ν] using
        hmap.projected_row_mem_profileSubspace S hS shift hshift
    have hle :=
      profileSubspace_le_zeroProfileConcreteNormalFormBasis_span (D.chart ν)
    exact hle hrow

/-- A concrete chart row map is a finite normal-form row classifier. -/
noncomputable def zeroProfileFiniteNormalFormRowClassifier_of_concreteRowMap
    {n L κ typeBudget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (D : ZeroProfileConcreteNormalFormData n κ typeBudget)
    (hmap : ZeroProfileConcreteNormalFormRowMap factors project D) :
    ZeroProfileFiniteNormalFormRowClassifier
      factors project
      (zeroProfileFiniteNormalFormFamilyData_of_concreteData D) where
  rowNormalForm := hmap.rowNormalForm
  projected_row_mem_normalFormSpace := by
    intro S hS shift hshift
    let ν := hmap.rowNormalForm S hS shift hshift
    have hrow :
        project (mlProj (shift * Finset.univ.prod factors)) ∈
          profileSubspace (D.profile ν) (D.chart ν).W := by
      simpa [ν] using
        hmap.projected_row_mem_profileSubspace S hS shift hshift
    have hle :=
      profileSubspace_le_zeroProfileConcreteNormalFormBasis_span (D.chart ν)
    exact hle hrow

/-- Concrete chart row maps close the projected common-span target through the
finite-normal-form classifier route. -/
theorem zeroProfileProjectedCommonSpanWithBudget_of_concreteRowMap
    {n L κ typeBudget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (D : ZeroProfileConcreteNormalFormData n κ typeBudget)
    (hmap : ZeroProfileConcreteNormalFormRowMap factors project D) :
    ZeroProfileProjectedCommonSpanWithBudget
      κ factors project typeBudget :=
  zeroProfileProjectedCommonSpanWithBudget_of_finiteNormalFormClassifier
    factors project
    (zeroProfileFiniteNormalFormFamilyData_of_concreteData D)
    (zeroProfileFiniteNormalFormRowClassifier_of_concreteRowMap
      factors project D hmap)

/-- The all-zero singleton profile budget fits the within-profile bound. -/
theorem zeroProfileSymmetricProfileDim_zeroProfileHistogram_le_withinProfileBound
    (κ : ℕ) :
    zeroProfileSymmetricProfileDim zeroProfileHistogram ≤
      withinProfileBound κ := by
  rw [zeroProfileSymmetricProfileDim_zeroProfileHistogram,
    withinProfileBound_eq_pow8]
  exact Nat.succ_le_of_lt (Nat.pow_pos (Nat.succ_pos κ))

/-- The direct `concreteW` row-embedding package gives a budgeted projected
common span for zero-profile rows at the identity projection. -/
theorem zeroProfileProjectedCommonSpanWithBudget_id_concreteW_of_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (LinearMap.id :
        MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) :=
  zeroProfileProjectedCommonSpanWithBudget_of_concreteRowMap
    (κ := Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (LinearMap.id :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
      (κ := Nat.log 2 n) hn4)
    (zeroProfileConcreteNormalFormRowMap_id_concreteW_of_rowEmbeddings
      M n hn htb hns hn4 hRowEmbeddings)

/-- The identity concrete normal-form span from `concreteW` can be pushed
through the singleton quotient projection with the same one-profile budget. -/
theorem zeroProfileProjectedCommonSpanWithBudget_singletonQuotient_concreteW_of_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    ZeroProfileProjectedCommonSpanWithBudget (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn htb hns).get i))
      (zeroProfileSymmetricProfileDim zeroProfileHistogram) :=
  zeroProfileProjectedCommonSpanWithBudget_of_id_projectedCommonSpan
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (zeroProfileQuotientBySingletonShiftProjection
      (fun i => (cookLevinFactorList M n hn htb hns).get i))
    (zeroProfileProjectedCommonSpanWithBudget_id_concreteW_of_rowEmbeddings
      M n hn htb hns hn4 hRowEmbeddings)

/-- The direct `concreteW` row-embedding package gives an actual finite
normal-form classifier for zero-profile rows at the identity projection. -/
noncomputable def zeroProfileFiniteNormalFormRowClassifier_id_concreteW_of_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    ZeroProfileFiniteNormalFormRowClassifier
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (LinearMap.id :
        MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
      (zeroProfileFiniteNormalFormFamilyData_of_concreteData
        (zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
          (κ := Nat.log 2 n) hn4)) :=
  zeroProfileFiniteNormalFormRowClassifier_of_concreteRowMap
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (LinearMap.id :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
      (κ := Nat.log 2 n) hn4)
    (zeroProfileConcreteNormalFormRowMap_id_concreteW_of_rowEmbeddings
      M n hn htb hns hn4 hRowEmbeddings)

/-- The concrete singleton zero-profile classifier gives the final
symmetric-power/profile finrank budget for the identity-projected
zero-profile shifted span. -/
theorem zeroProfileProjectedShiftSpan_finrank_le_withinProfileBound_id_concreteW_of_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    Module.finrank ℚ
        ↥(zeroProfileProjectedShiftSpan (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn htb hns).get i)
          (LinearMap.id :
            MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)) ≤
      withinProfileBound (Nat.log 2 n) := by
  exact
    (zeroProfileProjectedShiftSpan_finrank_le_of_commonSpanWithBudget_core
      (κ := Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (LinearMap.id :
        MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
      (zeroProfileProjectedCommonSpanWithBudget_id_concreteW_of_rowEmbeddings
        M n hn htb hns hn4 hRowEmbeddings)).trans
      (zeroProfileSymmetricProfileDim_zeroProfileHistogram_le_withinProfileBound
        (Nat.log 2 n))

/-- The existing concrete `concreteW` normal-form data proves the exact
singleton-quotient projected type budget.  This uses projection of the
identity common span, not shifted-support counting. -/
theorem zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_concreteW_of_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i) ≤
      withinProfileBound (Nat.log 2 n) :=
  (zeroProfileSingletonQuotientProjectedTypeBudget_le_of_id_projectedCommonSpan
    (κ := Nat.log 2 n)
    (factors := fun i => (cookLevinFactorList M n hn htb hns).get i)
    (zeroProfileProjectedCommonSpanWithBudget_id_concreteW_of_rowEmbeddings
      M n hn htb hns hn4 hRowEmbeddings)).trans
    (zeroProfileSymmetricProfileDim_zeroProfileHistogram_le_withinProfileBound
      (Nat.log 2 n))

/-- Concrete normal-form certificate: quotient projection, concrete
symmetric-power normal-form data, and the row typing into that data. -/
structure ZeroProfileConcreteNormalFormCertificate {n L κ : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (typeBudget : ℕ) where
  project : MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ
  project_idempotent : project.comp project = project
  killsSingleton : ZeroProfileProjectionKillsSingletonShifts factors project
  data : ZeroProfileConcreteNormalFormData n κ typeBudget
  rowMap : ZeroProfileConcreteNormalFormRowMap factors project data

/-- Concrete normal-form certificates instantiate the existing projected
normal-form certificate interface. -/
noncomputable def zeroProfileProjectedNormalFormCertificate_of_concreteCertificate
    {n L κ typeBudget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (cert :
      ZeroProfileConcreteNormalFormCertificate (κ := κ)
        factors typeBudget) :
    ZeroProfileProjectedNormalFormCertificate (κ := κ)
      factors typeBudget where
  project := cert.project
  project_idempotent := cert.project_idempotent
  killsSingleton := cert.killsSingleton
  family := zeroProfileProjectedNormalFormFamily_of_concreteData cert.data
  rowMap :=
    zeroProfileProjectedNormalFormRowMap_of_concreteRowMap
      factors cert.project cert.data cert.rowMap

/-- Cook-Levin concrete normal-form obligation for zero-profile rows. -/
def CookLevinZeroProfileConcreteNormalFormObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (typeBudget : ℕ) : Prop :=
  Nonempty
    (ZeroProfileConcreteNormalFormCertificate (κ := Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      typeBudget)

/-- The concrete normal-form obligation implies the previously exposed
projected-normal-form obligation. -/
theorem cookLevinZeroProfileProjectedNormalFormObligation_of_concreteNormalFormObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget : ℕ}
    (hconcrete :
      CookLevinZeroProfileConcreteNormalFormObligation
        M n hn htb hns typeBudget) :
    CookLevinZeroProfileProjectedNormalFormObligation
      M n hn htb hns typeBudget := by
  rcases hconcrete with ⟨cert⟩
  exact
    ⟨zeroProfileProjectedNormalFormCertificate_of_concreteCertificate
      (κ := Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      cert⟩

/-! ## Singleton-quotient concrete classifier close -/

/-- Paper-faithful zero-profile local normal-form classifier.

This is the Lean home for the manuscript's local finite-monoid/profile
compression lemma: a finite canonical alphabet, a concrete symmetric-power
chart for every canonical type, a classifier for each singleton-quotient
projected zero-profile Cook-Levin row, and the final profile-space budget.

The hard mathematical field is `rowMap`: it must prove that every projected
row lands in the symmetric-power span attached to its canonical local type. -/
structure CookLevinZeroProfileLocalNormalFormClassifier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (typeBudget : ℕ) where
  data :
    ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget
  rowMap :
    ZeroProfileConcreteNormalFormRowMap
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn htb hns).get i))
      data
  budget :
    typeBudget ≤ withinProfileBound (Nat.log 2 n)

/-- Prop form of the paper's zero-profile local normal-form classifier lemma.

This is the remaining mathematical input, not a raw-support count and not the
over-broad all-admissible-profile chart family. -/
def CookLevinZeroProfileLocalNormalFormClassifierObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ typeBudget : ℕ,
    Nonempty
      (CookLevinZeroProfileLocalNormalFormClassifier
        M n hn htb hns typeBudget)

/-- Concrete normal-form row typing for the singleton quotient closes the
quotiented zero-profile target with no `+ n` residual payment. -/
theorem cookLevinZeroProfileQuotientedShiftCommonSpan_of_concreteSingletonQuotientRowMap
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget : ℕ}
    (D : ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget)
    (hmap :
      ZeroProfileConcreteNormalFormRowMap
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn htb hns).get i))
        D)
    (hbudget : typeBudget ≤ withinProfileBound (Nat.log 2 n)) :
    CookLevinZeroProfileQuotientedShiftCommonSpan
      M n hn htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn htb hns).get i)) :=
  cookLevinZeroProfileQuotientedShiftCommonSpan_of_finiteNormalFormClassifier
    M n hn htb hns
    (zeroProfileFiniteNormalFormFamilyData_of_concreteData D)
    (zeroProfileFiniteNormalFormRowClassifier_of_concreteRowMap
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn htb hns).get i))
      D hmap)
    hbudget

/-- Concrete normal-form row typing proves the exact projected singleton
quotient type-budget inequality. -/
theorem zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_concreteRowMap
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget : ℕ}
    (D : ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget)
    (hmap :
      ZeroProfileConcreteNormalFormRowMap
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn htb hns).get i))
        D)
    (hbudget : typeBudget ≤ withinProfileBound (Nat.log 2 n)) :
    zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i) ≤
      withinProfileBound (Nat.log 2 n) :=
  zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_finiteNormalFormClassifier
    M n hn htb hns
    (zeroProfileFiniteNormalFormFamilyData_of_concreteData D)
    (zeroProfileFiniteNormalFormRowClassifier_of_concreteRowMap
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn htb hns).get i))
      D hmap)
    hbudget

namespace CookLevinZeroProfileLocalNormalFormClassifier

variable {M : DTM} {n typeBudget : ℕ} {hn : n ≥ 2}
  {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}

/-- The classifier exposes the concrete normal-form row-map data expected by
the existing singleton-quotient reducer. -/
theorem projectedTypeBudget_le
    (C :
      CookLevinZeroProfileLocalNormalFormClassifier
        M n hn htb hns typeBudget) :
    zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i) ≤
      withinProfileBound (Nat.log 2 n) :=
  zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_concreteRowMap
    M n hn htb hns C.data C.rowMap C.budget

/-- The classifier also closes the quotiented zero-profile common-span target
for the selected singleton quotient. -/
theorem quotientedShiftCommonSpan
    (C :
      CookLevinZeroProfileLocalNormalFormClassifier
        M n hn htb hns typeBudget) :
    CookLevinZeroProfileQuotientedShiftCommonSpan
      M n hn htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn htb hns).get i)) :=
  cookLevinZeroProfileQuotientedShiftCommonSpan_of_concreteSingletonQuotientRowMap
    M n hn htb hns C.data C.rowMap C.budget

end CookLevinZeroProfileLocalNormalFormClassifier

/-- The named local normal-form classifier obligation proves the exact
singleton-quotient projected budget. -/
theorem zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_localNormalFormClassifier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hclassifier :
      CookLevinZeroProfileLocalNormalFormClassifierObligation
        M n hn htb hns) :
    zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i) ≤
      withinProfileBound (Nat.log 2 n) := by
  rcases hclassifier with ⟨typeBudget, ⟨C⟩⟩
  exact C.projectedTypeBudget_le

/-- The same classifier obligation closes the quotiented zero-profile common
span consumed by Route B. -/
theorem cookLevinZeroProfileQuotientedShiftCommonSpan_of_localNormalFormClassifier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hclassifier :
      CookLevinZeroProfileLocalNormalFormClassifierObligation
        M n hn htb hns) :
    CookLevinZeroProfileQuotientedShiftCommonSpan
      M n hn htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn htb hns).get i)) := by
  rcases hclassifier with ⟨typeBudget, ⟨C⟩⟩
  exact C.quotientedShiftCommonSpan

/-! ## Boolean-normalized concrete classifier obstruction -/

/-- A concrete Boolean-normalized row map is, after forgetting the concrete
chart origin, exactly the existing Boolean normal-form obligation. -/
theorem cookLevinZeroProfileBooleanNormalFormObligation_of_concreteBooleanRowMap
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget : ℕ}
    (D : ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget)
    (hmap :
      ZeroProfileConcreteNormalFormRowMap
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        (zeroProfileBooleanNormalizeLinearMap (n := n))
        D) :
    CookLevinZeroProfileBooleanNormalFormObligation
      M n hn htb hns typeBudget :=
  ⟨zeroProfileProjectedNormalFormFamily_of_concreteData D,
    ⟨zeroProfileProjectedNormalFormRowMap_of_concreteRowMap
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (zeroProfileBooleanNormalizeLinearMap (n := n))
      D hmap⟩⟩

/-- Concrete Boolean-normalized normal forms inherit the singleton-row
obstruction: if the within-profile budget is already smaller than the ambient
variable count, no concrete Boolean row map can fit that budget. -/
theorem not_zeroProfileConcreteBooleanRowMap_of_withinProfileBound_lt_ambient
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget : ℕ}
    (D : ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget)
    (hbudget : typeBudget ≤ withinProfileBound (Nat.log 2 n))
    (hlt : withinProfileBound (Nat.log 2 n) < n) :
    ¬ Nonempty (ZeroProfileConcreteNormalFormRowMap
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        (zeroProfileBooleanNormalizeLinearMap (n := n))
        D) := by
  rintro ⟨hmap⟩
  exact
    not_cookLevinZeroProfileBooleanNormalFormObligation_of_withinProfileBound_lt_ambient
      M n hn htb hns hbudget hlt
      (cookLevinZeroProfileBooleanNormalFormObligation_of_concreteBooleanRowMap
        M n hn htb hns D hmap)

/-- At the paper endpoint `n = 2^804`, the concrete Boolean-normalized
classifier route cannot close within the paper's within-profile budget.  A
positive zero-profile close must therefore quotient/project away the singleton
directions rather than use Boolean normalization alone. -/
theorem not_zeroProfileConcreteBooleanRowMap_two_pow_804
    (M : DTM)
    (hn2 : (2 : ℕ) ^ 804 ≥ 2)
    (htb : M.timeBound ≤ 4)
    (hns : M.numStates ≤ (2 : ℕ) ^ 804)
    {typeBudget : ℕ}
    (D :
      ZeroProfileConcreteNormalFormData ((2 : ℕ) ^ 804)
        (Nat.log 2 ((2 : ℕ) ^ 804)) typeBudget)
    (hbudget :
      typeBudget ≤
        withinProfileBound (Nat.log 2 ((2 : ℕ) ^ 804))) :
    ¬ Nonempty (ZeroProfileConcreteNormalFormRowMap
        (fun i =>
          (cookLevinFactorList M ((2 : ℕ) ^ 804) hn2 htb hns).get i)
        (zeroProfileBooleanNormalizeLinearMap (n := (2 : ℕ) ^ 804))
        D) :=
  not_zeroProfileConcreteBooleanRowMap_of_withinProfileBound_lt_ambient
    M ((2 : ℕ) ^ 804) hn2 htb hns D
    hbudget withinProfileBound_log_two_pow_804_lt_ambient

/-- A concrete normal-form certificate plus residual payment closes the
unprojected zero-profile common-span bridge. -/
theorem cookLevinZeroHistogramShiftCommonSpan_of_concreteNormalFormCertificate_residualClosure
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget residualBudget : ℕ}
    (cert :
      ZeroProfileConcreteNormalFormCertificate (κ := Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        typeBudget)
    (hresidual :
      CookLevinZeroProfileProjectionResidualClosureWithBudget
        M n hn htb hns cert.project residualBudget)
    (hbudget :
      typeBudget + residualBudget ≤ withinProfileBound (Nat.log 2 n)) :
    CookLevinZeroHistogramShiftCommonSpan M n hn htb hns :=
  cookLevinZeroHistogramShiftCommonSpan_of_projectedNormalFormCertificate_residualClosure
    M n hn htb hns
    (zeroProfileProjectedNormalFormCertificate_of_concreteCertificate
      (κ := Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      cert)
    hresidual hbudget

/-- Residual-free concrete normal-form closure, when the projection fixes all
zero-profile shifted rows. -/
theorem cookLevinZeroHistogramShiftCommonSpan_of_concreteNormalFormCertificate_fixesShiftRows
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget : ℕ}
    (cert :
      ZeroProfileConcreteNormalFormCertificate (κ := Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        typeBudget)
    (hfix :
      CookLevinZeroProfileProjectionFixesShiftRows
        M n hn htb hns cert.project)
    (hbudget : typeBudget ≤ withinProfileBound (Nat.log 2 n)) :
    CookLevinZeroHistogramShiftCommonSpan M n hn htb hns :=
  cookLevinZeroHistogramShiftCommonSpan_of_projectedNormalFormCertificate_fixesShiftRows
    M n hn htb hns
    (zeroProfileProjectedNormalFormCertificate_of_concreteCertificate
      (κ := Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      cert)
    hfix hbudget

/-- Fully explicit zero-profile frontier: concrete normal forms, residual
payment, and the final within-profile budget inequality. -/
structure CookLevinZeroProfileConcreteNormalFormFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) where
  typeBudget : ℕ
  residualBudget : ℕ
  cert :
    ZeroProfileConcreteNormalFormCertificate (κ := Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      typeBudget
  residual :
    CookLevinZeroProfileProjectionResidualClosureWithBudget
      M n hn htb hns cert.project residualBudget
  budget :
    typeBudget + residualBudget ≤ withinProfileBound (Nat.log 2 n)

/-- The explicit concrete-normal-form frontier is sufficient for the
zero-profile histogram bridge. -/
theorem cookLevinZeroHistogramShiftCommonSpan_of_concreteNormalFormFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (frontier :
      CookLevinZeroProfileConcreteNormalFormFrontier
        M n hn htb hns) :
    CookLevinZeroHistogramShiftCommonSpan M n hn htb hns :=
  cookLevinZeroHistogramShiftCommonSpan_of_concreteNormalFormCertificate_residualClosure
    M n hn htb hns frontier.cert frontier.residual frontier.budget

/-! ## Axiom audit anchors -/

#print axioms zeroProfileConcreteNormalFormBasis_card_le_profileDim
#print axioms profileSubspace_le_zeroProfileConcreteNormalFormBasis_span
#print axioms zeroProfileConcreteLocalChart_of_submoduleFamily
#print axioms zeroProfileConcreteLocalChart_compiledCoefficientBasis
#print axioms zeroProfileConcreteLocalChart_concreteW
#print axioms zeroProfileSymmetricProfileDim_zeroProfileHistogram
#print axioms zeroProfileConcreteNormalFormData_singletonZeroProfile
#print axioms zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
#print axioms zeroProfileProjectedNormalFormFamily_of_concreteData
#print axioms zeroProfileFiniteNormalFormAlphabet_of_concreteData
#print axioms zeroProfileFiniteNormalFormFamilyData_of_concreteData
#print axioms zeroProfileConcreteNormalFormData_of_admissibleProfileCharts
#print axioms zeroProfileAdmissibleProfileChartFamily_compiledCoefficientBasis
#print axioms zeroProfileConcreteNormalFormRowMap_id_concreteW_of_rowEmbeddings
#print axioms zeroProfileProjectedNormalFormRowMap_of_concreteRowMap
#print axioms zeroProfileFiniteNormalFormRowClassifier_of_concreteRowMap
#print axioms zeroProfileProjectedCommonSpanWithBudget_of_concreteRowMap
#print axioms zeroProfileSymmetricProfileDim_zeroProfileHistogram_le_withinProfileBound
#print axioms zeroProfileProjectedCommonSpanWithBudget_id_concreteW_of_rowEmbeddings
#print axioms zeroProfileProjectedCommonSpanWithBudget_singletonQuotient_concreteW_of_rowEmbeddings
#print axioms zeroProfileFiniteNormalFormRowClassifier_id_concreteW_of_rowEmbeddings
#print axioms zeroProfileProjectedShiftSpan_finrank_le_withinProfileBound_id_concreteW_of_rowEmbeddings
#print axioms zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_concreteW_of_rowEmbeddings
#print axioms zeroProfileProjectedNormalFormCertificate_of_concreteCertificate
#print axioms cookLevinZeroProfileProjectedNormalFormObligation_of_concreteNormalFormObligation
#print axioms cookLevinZeroProfileQuotientedShiftCommonSpan_of_concreteSingletonQuotientRowMap
#print axioms zeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_concreteRowMap
#print axioms cookLevinZeroProfileBooleanNormalFormObligation_of_concreteBooleanRowMap
#print axioms not_zeroProfileConcreteBooleanRowMap_of_withinProfileBound_lt_ambient
#print axioms not_zeroProfileConcreteBooleanRowMap_two_pow_804
#print axioms cookLevinZeroHistogramShiftCommonSpan_of_concreteNormalFormCertificate_residualClosure
#print axioms cookLevinZeroHistogramShiftCommonSpan_of_concreteNormalFormCertificate_fixesShiftRows
#print axioms cookLevinZeroHistogramShiftCommonSpan_of_concreteNormalFormFrontier

end PathB
end DeepMath
end Paper93
end PallLean
