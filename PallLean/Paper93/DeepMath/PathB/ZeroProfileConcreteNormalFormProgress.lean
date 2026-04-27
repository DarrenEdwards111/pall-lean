import PallLean.Paper93.DeepMath.PathB.ZeroProfileNormalFormInstantiationProgress
import PallLean.Paper93.TensorDimBound

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
#print axioms zeroProfileProjectedNormalFormFamily_of_concreteData
#print axioms zeroProfileConcreteNormalFormData_of_admissibleProfileCharts
#print axioms zeroProfileProjectedNormalFormRowMap_of_concreteRowMap
#print axioms zeroProfileProjectedNormalFormCertificate_of_concreteCertificate
#print axioms cookLevinZeroProfileProjectedNormalFormObligation_of_concreteNormalFormObligation
#print axioms cookLevinZeroHistogramShiftCommonSpan_of_concreteNormalFormCertificate_residualClosure
#print axioms cookLevinZeroHistogramShiftCommonSpan_of_concreteNormalFormCertificate_fixesShiftRows
#print axioms cookLevinZeroHistogramShiftCommonSpan_of_concreteNormalFormFrontier

end PathB
end DeepMath
end Paper93
end PallLean
