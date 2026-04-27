import PallLean.Paper93.DeepMath.PathB.ZeroProfileQuotientTypeCompression

/-!
# Zero-profile normal-form instantiation progress

This file sharpens the quotient/type-space replacement from
`ZeroProfileQuotientTypeCompression`.

The older raw zero-profile shifted-row span is known to be too literal.  The
interface here instead asks for a finite family of projected normal forms.  Each
normal form carries a profile histogram and a local spanning family whose size
is bounded by the symmetric-power profile dimension

`∏ τ, Nat.choose (h τ + 2) 2`.

The resulting budget is a sum over normal forms, not the coarser
`card type * uniformLocalDim` budget from the first quotient interface.  Once a
projected row map is supplied, this proves the existing projected common-span
obligation.  Recovering the unprojected zero-profile bridge remains separated
through the residual closure/budget already exposed downstream.
-/

namespace PallLean
namespace Paper93
namespace DeepMath
namespace PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP SPDP
open scoped BigOperators

attribute [local instance] Classical.dec

/-! ## Symmetric-profile dimensions for projected normal forms -/

/-- The symmetric-power dimension budget for one profile histogram, using the
paper's constant local interface dimension three per effective type. -/
noncomputable def zeroProfileSymmetricProfileDim
    (h : ProfileHistogram) : ℕ :=
  ∏ τ : ConstraintType, Nat.choose (h τ + 2) 2

/-- The profile dimension estimate reused by the zero-profile normal-form
interface. -/
theorem zeroProfileSymmetricProfileDim_le_withinProfileBound
    (κ : ℕ) (h : ProfileHistogram)
    (hadm : ProfileAdmissible κ h) :
    zeroProfileSymmetricProfileDim h ≤ withinProfileBound κ := by
  simpa [zeroProfileSymmetricProfileDim] using
    (profileDimBound_le_withinProfileBound κ h hadm)

/-! ## Projected normal-form families -/

/-- A projected normal-form family for zero-profile rows.

The `normalForm` type is the finite local monoid / anonymous interface type
alphabet.  Its elements are allowed to have different profile histograms, so the
budget is the sharp sum of the corresponding symmetric-power dimensions. -/
structure ZeroProfileProjectedNormalFormFamily
    (n κ typeBudget : ℕ) where
  normalForm : Type
  [normalFormFintype : Fintype normalForm]
  profile : normalForm → ProfileHistogram
  profile_admissible : ∀ ν, ProfileAdmissible κ (profile ν)
  localBasis : normalForm → Finset (MvPolynomial (Fin n) ℚ)
  localBasis_card_le_profileDim :
    ∀ ν, (localBasis ν).card ≤ zeroProfileSymmetricProfileDim (profile ν)
  totalProfileBudget_le :
    (∑ ν : normalForm, zeroProfileSymmetricProfileDim (profile ν)) ≤
      typeBudget

/-- The local subspace represented by one projected normal form. -/
noncomputable def zeroProfileProjectedNormalFormSpace
    {n κ typeBudget : ℕ}
    (F : ZeroProfileProjectedNormalFormFamily n κ typeBudget)
    (ν : F.normalForm) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ
    (↑(F.localBasis ν) : Set (MvPolynomial (Fin n) ℚ))

/-- The dimension of one projected normal-form space is bounded by its
symmetric-power profile dimension. -/
theorem zeroProfileProjectedNormalFormSpace_finrank_le_profileDim
    {n κ typeBudget : ℕ}
    (F : ZeroProfileProjectedNormalFormFamily n κ typeBudget)
    (ν : F.normalForm) :
    Module.finrank ℚ ↥(zeroProfileProjectedNormalFormSpace F ν) ≤
      zeroProfileSymmetricProfileDim (F.profile ν) := by
  classical
  unfold zeroProfileProjectedNormalFormSpace
  exact (finrank_span_finset_le_card (F.localBasis ν)).trans
    (F.localBasis_card_le_profileDim ν)

/-- The global projected normal-form basis obtained by unioning all local
normal-form bases. -/
noncomputable def zeroProfileProjectedNormalFormGlobalBasis
    {n κ typeBudget : ℕ}
    (F : ZeroProfileProjectedNormalFormFamily n κ typeBudget) :
    Finset (MvPolynomial (Fin n) ℚ) := by
  classical
  letI : Fintype F.normalForm := F.normalFormFintype
  exact Finset.univ.biUnion F.localBasis

/-- The global normal-form basis fits in the explicit summed symmetric-profile
budget. -/
theorem zeroProfileProjectedNormalFormGlobalBasis_card_le_typeBudget
    {n κ typeBudget : ℕ}
    (F : ZeroProfileProjectedNormalFormFamily n κ typeBudget) :
    (zeroProfileProjectedNormalFormGlobalBasis F).card ≤ typeBudget := by
  classical
  letI : Fintype F.normalForm := F.normalFormFintype
  have hbi' :
      (Finset.univ.biUnion F.localBasis).card ≤
        ∑ ν ∈ (Finset.univ : Finset F.normalForm),
          (F.localBasis ν).card :=
    Finset.card_biUnion_le
  have hbi :
      (Finset.univ.biUnion F.localBasis).card ≤
        ∑ ν : F.normalForm, (F.localBasis ν).card := by
    simpa using hbi'
  have hsum' :
      (∑ ν ∈ (Finset.univ : Finset F.normalForm),
          (F.localBasis ν).card) ≤
        ∑ ν ∈ (Finset.univ : Finset F.normalForm),
          zeroProfileSymmetricProfileDim (F.profile ν) := by
    exact Finset.sum_le_sum (by
      intro ν _hν
      exact F.localBasis_card_le_profileDim ν)
  have hsum :
      (∑ ν : F.normalForm, (F.localBasis ν).card) ≤
        ∑ ν : F.normalForm,
          zeroProfileSymmetricProfileDim (F.profile ν) := by
    simpa using hsum'
  simpa [zeroProfileProjectedNormalFormGlobalBasis] using
    (hbi.trans (hsum.trans F.totalProfileBudget_le))

/-- The compressed projected span represented by the normal-form family. -/
noncomputable def zeroProfileProjectedNormalFormCompressedSpan
    {n κ typeBudget : ℕ}
    (F : ZeroProfileProjectedNormalFormFamily n κ typeBudget) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ
    (↑(zeroProfileProjectedNormalFormGlobalBasis F) :
      Set (MvPolynomial (Fin n) ℚ))

/-- One normal-form space is contained in the global projected normal-form
span. -/
theorem zeroProfileProjectedNormalFormSpace_le_compressedSpan
    {n κ typeBudget : ℕ}
    (F : ZeroProfileProjectedNormalFormFamily n κ typeBudget)
    (ν : F.normalForm) :
    zeroProfileProjectedNormalFormSpace F ν ≤
      zeroProfileProjectedNormalFormCompressedSpan F := by
  classical
  letI : Fintype F.normalForm := F.normalFormFintype
  unfold zeroProfileProjectedNormalFormSpace
    zeroProfileProjectedNormalFormCompressedSpan
  apply Submodule.span_mono
  intro q hq
  change q ∈ zeroProfileProjectedNormalFormGlobalBasis F
  unfold zeroProfileProjectedNormalFormGlobalBasis
  exact Finset.mem_biUnion.mpr ⟨ν, Finset.mem_univ ν, hq⟩

/-! ## Generator rows factor through projected normal forms -/

/-- A projected generator-to-normal-form map.

This is the concrete row typing still owed by the Cook-Levin proof: every
projected zero-profile generator row must be assigned a local normal form and
shown to land in that normal form's symmetric-profile span. -/
structure ZeroProfileProjectedNormalFormRowMap {n L κ typeBudget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (F : ZeroProfileProjectedNormalFormFamily n κ typeBudget) where
  rowNormalForm :
    ∀ (S : List (Fin n)), S.length ≤ κ →
      ∀ shift : MvPolynomial (Fin n) ℚ, shift.vars ⊆ S.toFinset →
        F.normalForm
  projected_row_mem_normalFormSpace :
    ∀ (S : List (Fin n)) (hS : S.length ≤ κ)
      (shift : MvPolynomial (Fin n) ℚ) (hshift : shift.vars ⊆ S.toFinset),
        project (mlProj (shift * Finset.univ.prod factors)) ∈
          zeroProfileProjectedNormalFormSpace F
            (rowNormalForm S hS shift hshift)

/-- A projected row map puts every projected row in the global normal-form
span. -/
theorem zeroProfileProjectedNormalFormRowMap_row_mem_compressedSpan
    {n L κ typeBudget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (F : ZeroProfileProjectedNormalFormFamily n κ typeBudget)
    (hmap : ZeroProfileProjectedNormalFormRowMap factors project F)
    (S : List (Fin n)) (hS : S.length ≤ κ)
    (shift : MvPolynomial (Fin n) ℚ) (hshift : shift.vars ⊆ S.toFinset) :
    project (mlProj (shift * Finset.univ.prod factors)) ∈
      zeroProfileProjectedNormalFormCompressedSpan F :=
  (zeroProfileProjectedNormalFormSpace_le_compressedSpan F
    (hmap.rowNormalForm S hS shift hshift))
    (hmap.projected_row_mem_normalFormSpace S hS shift hshift)

/-- Set-level containment of projected zero-profile rows in the normal-form
compressed span. -/
theorem zeroProfileProjectedShiftImageSet_subset_normalFormCompressedSpan
    {n L κ typeBudget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (F : ZeroProfileProjectedNormalFormFamily n κ typeBudget)
    (hmap : ZeroProfileProjectedNormalFormRowMap factors project F) :
    zeroProfileProjectedShiftImageSet κ factors project ⊆
      zeroProfileProjectedNormalFormCompressedSpan F := by
  intro q hq
  rcases hq with ⟨row, hrow, rfl⟩
  simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
    Set.mem_singleton_iff] at hrow
  rcases hrow with ⟨S, hS, shift, hshift, row_eq⟩
  rw [row_eq]
  exact zeroProfileProjectedNormalFormRowMap_row_mem_compressedSpan
    factors project F hmap S hS shift hshift

/-- A projected normal-form row map closes the existing projected
common-span-with-budget target. -/
theorem zeroProfileProjectedCommonSpanWithBudget_of_normalFormRowMap
    {n L κ typeBudget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (F : ZeroProfileProjectedNormalFormFamily n κ typeBudget)
    (hmap : ZeroProfileProjectedNormalFormRowMap factors project F) :
    ZeroProfileProjectedCommonSpanWithBudget
      κ factors project typeBudget := by
  classical
  refine ⟨zeroProfileProjectedNormalFormGlobalBasis F,
    zeroProfileProjectedNormalFormGlobalBasis_card_le_typeBudget F, ?_⟩
  simpa [zeroProfileProjectedNormalFormCompressedSpan] using
    zeroProfileProjectedShiftImageSet_subset_normalFormCompressedSpan
      factors project F hmap

/-! ## Certificates and Cook-Levin wrappers -/

/-- Projected normal-form certificate with the quotient projection data kept
explicit. -/
structure ZeroProfileProjectedNormalFormCertificate {n L κ : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (typeBudget : ℕ) where
  project : MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ
  project_idempotent : project.comp project = project
  killsSingleton : ZeroProfileProjectionKillsSingletonShifts factors project
  family : ZeroProfileProjectedNormalFormFamily n κ typeBudget
  rowMap : ZeroProfileProjectedNormalFormRowMap factors project family

/-- A projected normal-form certificate closes the projected common-span
target. -/
theorem zeroProfileProjectedCommonSpanWithBudget_of_normalFormCertificate
    {n L κ typeBudget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (cert :
      ZeroProfileProjectedNormalFormCertificate (κ := κ)
        factors typeBudget) :
    ZeroProfileProjectedCommonSpanWithBudget
      κ factors cert.project typeBudget :=
  zeroProfileProjectedCommonSpanWithBudget_of_normalFormRowMap
    factors cert.project cert.family cert.rowMap

/-- Cook-Levin projected normal-form obligation.  This is the sharper
replacement for the failed raw shifted-row support route. -/
def CookLevinZeroProfileProjectedNormalFormObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (typeBudget : ℕ) : Prop :=
  Nonempty
    (ZeroProfileProjectedNormalFormCertificate (κ := Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      typeBudget)

/-- The sharper projected normal-form obligation implies the existing
projected common-span obligation. -/
theorem cookLevinZeroProfileProjectedCommonSpanObligation_of_projectedNormalFormObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget : ℕ}
    (hnf :
      CookLevinZeroProfileProjectedNormalFormObligation
        M n hn htb hns typeBudget) :
    CookLevinZeroProfileProjectedCommonSpanObligation
      M n hn htb hns typeBudget := by
  rcases hnf with ⟨cert⟩
  exact
    ⟨cert.project, cert.project_idempotent, cert.killsSingleton,
      zeroProfileProjectedCommonSpanWithBudget_of_normalFormCertificate
        (κ := Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        cert⟩

/-- Residual-free version: if the chosen projection fixes every zero-profile
row, the residual budget is zero.  This names the alternative to separately
paying residual singleton/linear rows. -/
def ZeroProfileProjectionFixesShiftRows {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) : Prop :=
  ∀ q ∈ zeroProfileShiftImageSet κ factors, project q = q

/-- If the projection fixes the whole zero-profile shifted family, the residual
closure is free. -/
theorem zeroProfileProjectionResidualClosureWithBudget_zero_of_fixesShiftRows
    {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hfix : ZeroProfileProjectionFixesShiftRows κ factors project) :
    ZeroProfileProjectionResidualClosureWithBudget κ factors project 0 := by
  classical
  refine ⟨∅, by simp, ?_⟩
  intro q hq
  have hzero : q - project q = 0 := by
    rw [hfix q hq]
    simp
  rw [hzero]
  exact Submodule.zero_mem _

/-! ## Singleton-shift obstruction to residual-free quotienting -/

/-- The singleton-shift zero-profile row attached to a base product. -/
noncomputable def zeroProfileSingletonShiftRow {n : ℕ}
    (p : MvPolynomial (Fin n) ℚ) (i : Fin n) :
    MvPolynomial (Fin n) ℚ :=
  mlProj (MvPolynomial.X i * p)

/-- Singleton-shift rows have a Kronecker coefficient matrix at the degree-one
monomials, with diagonal entry the base product's constant coefficient. -/
theorem zeroProfileSingletonShiftRow_coeff_single
    {n : ℕ} (p : MvPolynomial (Fin n) ℚ) (i j : Fin n) :
    MvPolynomial.coeff (Finsupp.single i 1)
        (zeroProfileSingletonShiftRow p j) =
      if i = j then
        MvPolynomial.coeff (0 : Fin n →₀ ℕ) p
      else 0 := by
  classical
  unfold zeroProfileSingletonShiftRow
  rw [coeff_mlProj_of_isMultilinear_mono]
  · rw [MvPolynomial.coeff_X_mul']
    by_cases hij : i = j
    · subst j
      have hmem :
          i ∈ (Finsupp.single i 1 : Fin n →₀ ℕ).support := by
        simp
      rw [if_pos hmem, if_pos rfl]
      simp
    · have hnot :
          j ∉ (Finsupp.single i 1 : Fin n →₀ ℕ).support := by
        rw [Finsupp.mem_support_iff]
        simp [hij]
      rw [if_neg hnot, if_neg hij]
  · intro k
    simp [Finsupp.single_apply]
    split_ifs <;> omega

/-- If the base product has nonzero constant coefficient, the singleton-shift
rows are linearly independent.  This is the concrete obstruction that raw
singleton residuals create for any quotient projection that kills them. -/
theorem zeroProfileSingletonShiftRows_linearIndependent_of_constCoeff_ne_zero
    {n : ℕ} (p : MvPolynomial (Fin n) ℚ)
    (hp0 : MvPolynomial.coeff (0 : Fin n →₀ ℕ) p ≠ 0) :
    LinearIndependent ℚ (fun i : Fin n =>
      zeroProfileSingletonShiftRow p i) := by
  classical
  rw [linearIndependent_iff']
  intro s w hw i hi
  have hcoeff := congrArg
    (fun q => MvPolynomial.coeff (Finsupp.single (i : Fin n) 1) q) hw
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    smul_eq_mul, MvPolynomial.coeff_zero] at hcoeff
  have hsum :
      (∑ j ∈ s,
          w j *
            MvPolynomial.coeff (Finsupp.single (i : Fin n) 1)
              (zeroProfileSingletonShiftRow p j)) =
        w i * MvPolynomial.coeff (0 : Fin n →₀ ℕ) p := by
    calc
      (∑ j ∈ s,
          w j *
            MvPolynomial.coeff (Finsupp.single (i : Fin n) 1)
              (zeroProfileSingletonShiftRow p j))
          = ∑ j ∈ s,
              w j *
                (if i = j then
                  MvPolynomial.coeff (0 : Fin n →₀ ℕ) p
                else 0) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            rw [zeroProfileSingletonShiftRow_coeff_single]
      _ = w i * MvPolynomial.coeff (0 : Fin n →₀ ℕ) p := by
            rw [Finset.sum_eq_single i]
            · simp
            · intro j hj hji
              have hij : i ≠ j := by
                intro heq
                exact hji heq.symm
              simp [hij]
            · intro hnot
              exact False.elim (hnot hi)
  rw [hsum] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_right hp0

/-- A singleton-shift row is one of the zero-profile shifted rows whenever
the window budget permits one touched variable. -/
theorem zeroProfileSingletonShiftRow_mem_shiftImageSet
    {n L κ : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (i : Fin n) (hκ : 1 ≤ κ) :
    zeroProfileSingletonShiftRow (Finset.univ.prod factors) i ∈
      zeroProfileShiftImageSet κ factors := by
  classical
  simp only [zeroProfileShiftImageSet, Set.mem_iUnion,
    Set.mem_singleton_iff]
  refine ⟨[i], ?_, MvPolynomial.X i, ?_, rfl⟩
  · simpa using hκ
  · intro v hv
    simpa using hv

/-- A quotient projection that kills singleton shifts cannot also fix every
zero-profile shifted row when the base product has nonzero constant
coefficient. -/
theorem not_zeroProfileProjectionFixesShiftRows_of_killsSingleton_constCoeff_ne_zero
    {n L κ : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (i : Fin n) (hκ : 1 ≤ κ)
    (hp0 :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (Finset.univ.prod factors) ≠ 0)
    (hkills : ZeroProfileProjectionKillsSingletonShifts factors project) :
    ¬ ZeroProfileProjectionFixesShiftRows κ factors project := by
  intro hfix
  let q := zeroProfileSingletonShiftRow (Finset.univ.prod factors) i
  have hqmem : q ∈ zeroProfileShiftImageSet κ factors :=
    zeroProfileSingletonShiftRow_mem_shiftImageSet factors i hκ
  have hfixed : project q = q := hfix q hqmem
  have hkill : project q = 0 := hkills i
  have hqzero : q = 0 := by
    rw [← hfixed, hkill]
  have hcoeff_zero :
      MvPolynomial.coeff (Finsupp.single i 1) q = 0 := by
    rw [hqzero, MvPolynomial.coeff_zero]
  have hcoeff_one :
      MvPolynomial.coeff (Finsupp.single i 1) q =
        MvPolynomial.coeff (0 : Fin n →₀ ℕ)
          (Finset.univ.prod factors) := by
    simp [q, zeroProfileSingletonShiftRow_coeff_single]
  exact hp0 (hcoeff_one ▸ hcoeff_zero)

/-- Any residual span for a projection that kills the singleton-shift rows must
pay at least the ambient variable count.  This is a lower bound, not another
frontier assumption: it follows from the Kronecker coefficient matrix above. -/
theorem zeroProfileProjectionResidualClosureWithBudget_residualBudget_ge_ambient_of_killsSingleton_constCoeff_ne_zero
    {n L κ residualBudget : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hκ : 1 ≤ κ)
    (hp0 :
      MvPolynomial.coeff (0 : Fin n →₀ ℕ)
        (Finset.univ.prod factors) ≠ 0)
    (hkills : ZeroProfileProjectionKillsSingletonShifts factors project)
    (hresidual :
      ZeroProfileProjectionResidualClosureWithBudget
        κ factors project residualBudget) :
    n ≤ residualBudget := by
  classical
  rcases hresidual with ⟨R, hR_card, hR_span⟩
  let U : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    Submodule.span ℚ (↑R : Set (MvPolynomial (Fin n) ℚ))
  haveI hU_finite : Module.Finite ℚ ↥U :=
    Module.Finite.span_of_finite ℚ (Finset.finite_toSet R)
  have hrow_mem : ∀ i : Fin n,
      zeroProfileSingletonShiftRow (Finset.univ.prod factors) i ∈ U := by
    intro i
    have hshift :
        zeroProfileSingletonShiftRow (Finset.univ.prod factors) i ∈
          zeroProfileShiftImageSet κ factors :=
      zeroProfileSingletonShiftRow_mem_shiftImageSet factors i hκ
    have hres :
        zeroProfileSingletonShiftRow (Finset.univ.prod factors) i -
            project (zeroProfileSingletonShiftRow
              (Finset.univ.prod factors) i) ∈ U :=
      hR_span _ hshift
    have hkill :
        project (zeroProfileSingletonShiftRow
          (Finset.univ.prod factors) i) = 0 :=
      hkills i
    simpa [U, hkill] using hres
  let rowsInU : Fin n → U :=
    fun i => ⟨zeroProfileSingletonShiftRow
      (Finset.univ.prod factors) i, hrow_mem i⟩
  have hli :
      LinearIndependent ℚ
        (fun i : Fin n =>
          zeroProfileSingletonShiftRow (Finset.univ.prod factors) i) :=
    zeroProfileSingletonShiftRows_linearIndependent_of_constCoeff_ne_zero
      (Finset.univ.prod factors) hp0
  have hli_U : LinearIndependent ℚ rowsInU := by
    rw [linearIndependent_iff'] at hli ⊢
    intro s w hw i hi
    apply hli s w ?_ i hi
    have hval := congrArg
      (fun q : U => (q : MvPolynomial (Fin n) ℚ)) hw
    simpa [rowsInU] using hval
  have hcard_le_finrank :
      n ≤ Module.finrank ℚ ↥U := by
    simpa [Fintype.card_fin] using hli_U.fintype_card_le_finrank
  have hfinrank_le_card :
      Module.finrank ℚ ↥U ≤ R.card := by
    simpa [U] using
      (finrank_span_finset_le_card R :
        Module.finrank ℚ
          ↥(Submodule.span ℚ
            (↑R : Set (MvPolynomial (Fin n) ℚ))) ≤ R.card)
  exact hcard_le_finrank.trans (hfinrank_le_card.trans hR_card)

/-- Cook-Levin version of projection-fixes-shift-rows. -/
def CookLevinZeroProfileProjectionFixesShiftRows
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ) : Prop :=
  ZeroProfileProjectionFixesShiftRows (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    project

/-- The actual Cook-Levin base product has nonzero constant coefficient, so any
singleton-killing quotient projection cannot be residual-free. -/
theorem not_CookLevinZeroProfileProjectionFixesShiftRows_of_killsSingleton_actual
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hkills :
      ZeroProfileProjectionKillsSingletonShifts
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        project) :
    ¬ CookLevinZeroProfileProjectionFixesShiftRows
        M n hn htb hns project := by
  have hlog_pos : 0 < Nat.log 2 n := Nat.log_pos (by omega) hn
  exact
    not_zeroProfileProjectionFixesShiftRows_of_killsSingleton_constCoeff_ne_zero
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      project
      ⟨0, by omega⟩
      (Nat.succ_le_of_lt hlog_pos)
      (by
        simpa [cookLevinZeroProfileBaseProduct] using
          (show
            MvPolynomial.coeff (0 : Fin n →₀ ℕ)
              (cookLevinZeroProfileBaseProduct M n hn htb hns) ≠ 0
            from by
              rw [cookLevinZeroProfileBaseProduct_coeff_zero
                M n hn htb hns]
              norm_num))
      hkills

/-- For the actual Cook-Levin base product, any residual closure for a
singleton-killing quotient projection must pay at least `n` rows.  Thus a
paper-scale zero-profile close cannot use a free/fixed projection residual. -/
theorem cookLevinZeroProfileProjectionResidualClosureWithBudget_residualBudget_ge_ambient_of_killsSingleton_actual
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {residualBudget : ℕ}
    (project :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] MvPolynomial (Fin n) ℚ)
    (hkills :
      ZeroProfileProjectionKillsSingletonShifts
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        project)
    (hresidual :
      CookLevinZeroProfileProjectionResidualClosureWithBudget
        M n hn htb hns project residualBudget) :
    n ≤ residualBudget := by
  have hlog_pos : 0 < Nat.log 2 n := Nat.log_pos (by omega) hn
  exact
    zeroProfileProjectionResidualClosureWithBudget_residualBudget_ge_ambient_of_killsSingleton_constCoeff_ne_zero
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      project
      (Nat.succ_le_of_lt hlog_pos)
      (by
        simpa [cookLevinZeroProfileBaseProduct] using
          (show
            MvPolynomial.coeff (0 : Fin n →₀ ℕ)
              (cookLevinZeroProfileBaseProduct M n hn htb hns) ≠ 0
            from by
              rw [cookLevinZeroProfileBaseProduct_coeff_zero
                M n hn htb hns]
              norm_num))
      hkills
      hresidual

/-- A projected normal-form certificate plus a paid residual closes the
unprojected non-scalar zero-profile budget. -/
theorem cookLevinZeroProfileNonScalarClosureWithBudget_of_projectedNormalFormCertificate_residualClosure
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget residualBudget budget : ℕ}
    (cert :
      ZeroProfileProjectedNormalFormCertificate (κ := Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        typeBudget)
    (hresidual :
      CookLevinZeroProfileProjectionResidualClosureWithBudget
        M n hn htb hns cert.project residualBudget)
    (hbudget : typeBudget + residualBudget ≤ budget) :
    CookLevinZeroProfileNonScalarClosureWithBudget
      M n hn htb hns budget := by
  simpa [CookLevinZeroProfileNonScalarClosureWithBudget,
    CookLevinZeroProfileProjectionResidualClosureWithBudget,
    ZeroProfileCompressedSpanCommonSpanWithBudget] using
    (zeroProfileCompressedSpanCommonSpanWithBudget_of_projectedCommonSpan_residualClosure
      (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      cert.project
      (zeroProfileProjectedCommonSpanWithBudget_of_normalFormCertificate
        (κ := Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        cert)
      hresidual hbudget)

/-- A projected normal-form certificate plus residual payment fitting inside
`withinProfileBound` closes the existing zero histogram common-span bridge. -/
theorem cookLevinZeroHistogramShiftCommonSpan_of_projectedNormalFormCertificate_residualClosure
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget residualBudget : ℕ}
    (cert :
      ZeroProfileProjectedNormalFormCertificate (κ := Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        typeBudget)
    (hresidual :
      CookLevinZeroProfileProjectionResidualClosureWithBudget
        M n hn htb hns cert.project residualBudget)
    (hbudget :
      typeBudget + residualBudget ≤ withinProfileBound (Nat.log 2 n)) :
    CookLevinZeroHistogramShiftCommonSpan M n hn htb hns :=
  cookLevinZeroHistogramShiftCommonSpan_of_nonScalarClosureWithBudget
    M n hn htb hns
    (cookLevinZeroProfileNonScalarClosureWithBudget_of_projectedNormalFormCertificate_residualClosure
      M n hn htb hns
      (budget := typeBudget + residualBudget)
      cert hresidual le_rfl)
    hbudget

/-- A residual-free projected normal-form certificate closes the zero histogram
bridge using only the type budget. -/
theorem cookLevinZeroHistogramShiftCommonSpan_of_projectedNormalFormCertificate_fixesShiftRows
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    {typeBudget : ℕ}
    (cert :
      ZeroProfileProjectedNormalFormCertificate (κ := Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        typeBudget)
    (hfix :
      CookLevinZeroProfileProjectionFixesShiftRows
        M n hn htb hns cert.project)
    (hbudget : typeBudget ≤ withinProfileBound (Nat.log 2 n)) :
    CookLevinZeroHistogramShiftCommonSpan M n hn htb hns := by
  apply
    cookLevinZeroHistogramShiftCommonSpan_of_projectedNormalFormCertificate_residualClosure
      M n hn htb hns cert
  · simpa [CookLevinZeroProfileProjectionResidualClosureWithBudget,
      CookLevinZeroProfileProjectionFixesShiftRows] using
      zeroProfileProjectionResidualClosureWithBudget_zero_of_fixesShiftRows
        (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
        cert.project hfix
  · simpa using hbudget

/-! ## Axiom audit anchors -/

#print axioms zeroProfileSymmetricProfileDim_le_withinProfileBound
#print axioms zeroProfileProjectedNormalFormSpace_finrank_le_profileDim
#print axioms zeroProfileProjectedNormalFormGlobalBasis_card_le_typeBudget
#print axioms zeroProfileProjectedNormalFormSpace_le_compressedSpan
#print axioms zeroProfileProjectedShiftImageSet_subset_normalFormCompressedSpan
#print axioms zeroProfileProjectedCommonSpanWithBudget_of_normalFormRowMap
#print axioms zeroProfileProjectedCommonSpanWithBudget_of_normalFormCertificate
#print axioms cookLevinZeroProfileProjectedCommonSpanObligation_of_projectedNormalFormObligation
#print axioms zeroProfileProjectionResidualClosureWithBudget_zero_of_fixesShiftRows
#print axioms zeroProfileSingletonShiftRow_coeff_single
#print axioms zeroProfileSingletonShiftRows_linearIndependent_of_constCoeff_ne_zero
#print axioms not_zeroProfileProjectionFixesShiftRows_of_killsSingleton_constCoeff_ne_zero
#print axioms zeroProfileProjectionResidualClosureWithBudget_residualBudget_ge_ambient_of_killsSingleton_constCoeff_ne_zero
#print axioms not_CookLevinZeroProfileProjectionFixesShiftRows_of_killsSingleton_actual
#print axioms cookLevinZeroProfileProjectionResidualClosureWithBudget_residualBudget_ge_ambient_of_killsSingleton_actual
#print axioms cookLevinZeroProfileNonScalarClosureWithBudget_of_projectedNormalFormCertificate_residualClosure
#print axioms cookLevinZeroHistogramShiftCommonSpan_of_projectedNormalFormCertificate_residualClosure
#print axioms cookLevinZeroHistogramShiftCommonSpan_of_projectedNormalFormCertificate_fixesShiftRows

end PathB
end DeepMath
end Paper93
end PallLean
