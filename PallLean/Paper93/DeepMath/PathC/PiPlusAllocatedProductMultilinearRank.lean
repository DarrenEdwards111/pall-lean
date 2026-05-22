import PallLean.Paper93.DeepMath.PathC.PiPlusDistributedStabilityAllocationFactors
import PallLean.Paper93.DeepMath.PathC.PiPlusPaperRemark21MultilinearizeRank
import PallLean.Paper93.Lemma31ProfileSubspaceCompiledBasis

/-!
# Allocated product normalization at the rank level

This file composes the exact allocated-product Boolean normalization theorem with
Remark 21's rank-level multilinearization inequality.  The point is deliberately
narrow: the normalized factor product is the Boolean representative of the
allocated derivative product, while the rank bound is paid for at the raw
allocated-product row space.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open WithinProfileBound
open SymmetricPowerBound

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- The normalized product of the individually normalized allocated derivative
factors, kept as an expression-level abbreviation so later row-certificate
lemmas can point to the exact product that appears after quotient
normalization. -/
noncomputable abbrev piPlusBooleanProjectedAllocatedNormalizedFactorProduct
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ :=
  Finset.univ.prod (fun i : Fin (piPlusBooleanProjectedTransformedConstraintFactors
      M n hn2 htb hns D).length =>
    zeroProfileBooleanNormalize
      (iterDerivList (alloc i)
        (piPlusBooleanProjectedTransformedConstraintFactors
          M n hn2 htb hns D)[i.val]))

/-- Exact Boolean-representative statement for the allocated Leibniz product:
multilinearizing the allocated derivative product is the same Boolean object as
multilinearizing the product of the normalized local derivative factors. -/
theorem multilinearize_allocatedDerivativeProduct_eq_normalizedFactorProduct
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    multilinearize
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) =
      multilinearize
        (piPlusBooleanProjectedAllocatedNormalizedFactorProduct
          M n hn2 htb hns D alloc) := by
  apply BoolPoly.ext
  simp only [coe_multilinearize]
  exact zeroProfileBooleanNormalize_allocatedDerivativeProduct_eq_normalizedFactorProduct
    M n hn2 htb hns D alloc

/-- Rank-level form of the previous equality plus Remark 21.  The normalized
factor product is identified as the Boolean representative, but the SPDP rank
cost is bounded by the raw allocated-product row space.  This is the exact
normalization/rank handoff needed before the remaining Booleanity row
certificate synthesis. -/
theorem allocatedNormalizedFactorProduct_multilinearizedRank_le_rawAllocatedProductRank
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : ℕ) :
    multilinearize
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) =
      multilinearize
        (piPlusBooleanProjectedAllocatedNormalizedFactorProduct
          M n hn2 htb hns D alloc) ∧
    rkSPDP_multilinearized B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ≤
      rkSPDP B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) := by
  exact ⟨
    multilinearize_allocatedDerivativeProduct_eq_normalizedFactorProduct
      M n hn2 htb hns D alloc,
    multilinearize_rank_le_direct B κ ℓ
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc)⟩


/-! ## Raw allocated-product rank from a finite profile cover

The normalization handoff above leaves the real P-side cost at the raw row
space of the allocated derivative product.  The next lemmas isolate the exact
linear-algebra closeout needed after the Leibniz/profile work: if every raw
SPDP generator row is covered by a finite sum of profile-compressed spaces, and
each such space has the Lemma-31 dimension budget, then the raw rank is bounded
by `number_of_spaces * withinProfileBound κ`.
-/

/-- Kernel-clean finite-cover rank bound for raw SPDP rows.  This is just
`Submodule.finrank_mono` followed by the finite `iSup` dimension inequality and
the per-summand dimension budgets. -/
theorem rawRank_le_sum_subspaces_of_rawSubspace_le {N r : Nat}
    (B : BlockPartition N) (κ ℓ C : Nat)
    (p : MvPolynomial (Fin N) ℚ)
    (W : Fin r → Submodule ℚ (MvPolynomial (Fin N) ℚ))
    [∀ i, Module.Finite ℚ (W i)]
    (hcover : rawBlockedSpdpSubspace B κ ℓ p ≤ ⨆ i : Fin r, W i)
    (hdim : ∀ i : Fin r, Module.finrank ℚ (W i) ≤ C) :
    rkSPDP B κ ℓ p ≤ r * C := by
  unfold rkSPDP rawBlockedSpdpRank
  calc
    Module.finrank ℚ (rawBlockedSpdpSubspace B κ ℓ p)
        ≤ Module.finrank ℚ ↥(⨆ i : Fin r, W i) :=
          Submodule.finrank_mono hcover
    _ ≤ ∑ i : Fin r, Module.finrank ℚ (W i) :=
          finrank_iSup_fin_le r W
    _ ≤ ∑ _i : Fin r, C :=
          Finset.sum_le_sum (fun i _hi => hdim i)
    _ = r * C := by
          simp [Finset.sum_const]

/-- Generator-row form of `rawRank_le_sum_subspaces_of_rawSubspace_le`: it is
enough to classify each raw generator `m * ∂_S p` into the finite profile cover.
This is the form consumed by a Leibniz expansion proof. -/
theorem rawRank_le_sum_subspaces_of_generator_rows {N r : Nat}
    (B : BlockPartition N) (κ ℓ C : Nat)
    (p : MvPolynomial (Fin N) ℚ)
    (W : Fin r → Submodule ℚ (MvPolynomial (Fin N) ℚ))
    [∀ i, Module.Finite ℚ (W i)]
    (hrow : ∀ (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible B S →
      m * iterDerivList S p ∈ ⨆ i : Fin r, W i)
    (hdim : ∀ i : Fin r, Module.finrank ℚ (W i) ≤ C) :
    rkSPDP B κ ℓ p ≤ r * C := by
  refine rawRank_le_sum_subspaces_of_rawSubspace_le B κ ℓ C p W ?_ hdim
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, m, hSlen, hmdeg, hmvars, hadm, rfl⟩
  exact hrow S m hSlen hmdeg hmvars hadm

/-- Allocated-product specialization with a Lemma-31-style budget.  Once the
Leibniz expansion plus per-factor/profile compression proves the generator-row
cover into `W`, the raw rank of the allocated derivative product is bounded by
`r * withinProfileBound κ`. -/
theorem allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows
    {r : Nat}
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (W : Fin r → Submodule ℚ
      (MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ))
    [∀ i, Module.Finite ℚ (W i)]
    (hrow : ∀
      (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible B S →
      m * iterDerivList S
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ∈ ⨆ i : Fin r, W i)
    (hdim : ∀ i : Fin r, Module.finrank ℚ (W i) ≤ withinProfileBound κ) :
    rkSPDP B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ≤
      r * withinProfileBound κ := by
  exact rawRank_le_sum_subspaces_of_generator_rows B κ ℓ (withinProfileBound κ)
    (piPlusBooleanProjectedAllocatedDerivativeProduct M n hn2 htb hns D alloc)
    W hrow hdim

/-- Paper-scale name for the allocated-product raw rank target.  The only
remaining mathematical input is the `hrow` classifier: expand raw rows by
Leibniz, classify each per-factor derivative into its local span, place each
summand in one of the finite profile-compressed spaces `W`, then use Lemma 31 to
discharge `hdim`. -/
theorem paperScale_allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows
    {r : Nat}
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (κ ℓ : Nat)
    (W : Fin r → Submodule ℚ
      (MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ))
    [∀ i, Module.Finite ℚ (W i)]
    (hrow : ∀
      (S : List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
      (m : MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition S →
      m * iterDerivList S
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc) ∈
        ⨆ i : Fin r, W i)
    (hdim : ∀ i : Fin r, Module.finrank ℚ (W i) ≤ withinProfileBound κ) :
    rkSPDP
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc) ≤
      r * withinProfileBound κ := by
  exact allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    alloc
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ W hrow hdim



/-! ## Admissible-profile cover for the allocated-product `hrow` classifier -/

/-- The finite type of genuinely admissible profiles at radius `κ`.  This is the
right index type for the raw allocated-product cover: every Leibniz distribution
partitioning an SPDP derivative list has total profile mass at most `κ`, so it
selects an element of this subtype rather than merely a bounded profile. -/
def AdmissibleProfile (κ : Nat) : Type :=
  { h : ProfileHistogram // ProfileAdmissible κ h }

namespace AdmissibleProfile

/-- Forget an admissible profile to the existing bounded-profile enumeration. -/
def toBoundedProfile {κ : Nat} (ap : AdmissibleProfile κ) : BoundedProfile κ :=
  admissibleToBounded ap.property

@[simp] theorem toBoundedProfile_toHistogram {κ : Nat}
    (ap : AdmissibleProfile κ) :
    ap.toBoundedProfile.toHistogram = ap.val := rfl

noncomputable instance (κ : Nat) : Fintype (AdmissibleProfile κ) := by
  classical
  exact Fintype.ofInjective
    (fun ap : AdmissibleProfile κ => ap.toBoundedProfile)
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg BoundedProfile.toHistogram h)

end AdmissibleProfile

/-- Number of admissible profiles in the raw allocated-product profile cover. -/
noncomputable abbrev admissibleProfileCoverCard (κ : Nat) : Nat :=
  Fintype.card (AdmissibleProfile κ)

/-- Enumeration of admissible profiles by `Fin admissibleProfileCoverCard`. -/
noncomputable abbrev admissibleProfileCoverEnum (κ : Nat) :
    Fin (admissibleProfileCoverCard κ) → AdmissibleProfile κ :=
  (Fintype.equivFin (AdmissibleProfile κ)).symm

/-- The natural Lemma-31 profile cover space
`V_h = profileSubspace h (interfaceSpace_compiledBasis B κ ℓ)`. -/
noncomputable abbrev admissibleProfileCoverSpace {N : Nat}
    (B : BlockPartition N) (κ ℓ : Nat) :
    Fin (admissibleProfileCoverCard κ) →
      Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
  fun i => profileSubspace ((admissibleProfileCoverEnum κ i).val)
    (fun σ : ConstraintType => PallLean.Paper93.interfaceSpace_compiledBasis B κ ℓ σ)

/-- Generic finite-dimensionality of `profileSubspace` from finite-dimensional
per-type interface spaces.  Kept local here so the raw-rank closeout can provide
the `Module.Finite` instances required by `finrank_iSup_fin_le`. -/
theorem profileSubspace_finite_of_finite_local
    {N : Nat} (h : ProfileHistogram)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin N) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ (W τ)) :
    Module.Finite ℚ (profileSubspace h W) := by
  classical
  unfold profileSubspace
  set d : ConstraintType → Nat := fun τ => Module.finrank ℚ (W τ) with hd_def
  let b : ∀ τ, Module.Basis (Fin (d τ)) ℚ (W τ) :=
    fun τ => Module.finBasis ℚ (W τ)
  have hle :
      profileSubspace h W ≤
        Submodule.span ℚ
          (Set.range (profileSymProd W b : ProfileIndex h d → _)) :=
    profileSubspace_le_profileSymProd_span W b
  haveI hfin_big : Module.Finite ℚ
      (Submodule.span ℚ
        (Set.range (profileSymProd W b : ProfileIndex h d → _))) := by
    apply Module.Finite.span_of_finite
    exact Set.finite_range _
  exact Module.Finite.of_injective
    ((Submodule.inclusion hle) : _ →ₗ[ℚ] _)
    (Submodule.inclusion_injective hle)

/-- Each admissible-profile cover space is finite-dimensional. -/
theorem admissibleProfileCoverSpace_finite {N : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (i : Fin (admissibleProfileCoverCard κ)) :
    Module.Finite ℚ (admissibleProfileCoverSpace B κ ℓ i) := by
  classical
  exact profileSubspace_finite_of_finite_local
    ((admissibleProfileCoverEnum κ i).val)
    (fun σ : ConstraintType => PallLean.Paper93.interfaceSpace_compiledBasis B κ ℓ σ)
    (fun σ => PallLean.Paper93.interfaceSpace_compiledBasis_finite B κ ℓ σ)

/-- Step (c): the `hdim` side of `hrow`, discharged directly by Lemma 31 for
compiled-basis profile subspaces. -/
theorem admissibleProfileCoverSpace_finrank_le_withinProfileBound {N : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (i : Fin (admissibleProfileCoverCard κ)) :
    Module.finrank ℚ (admissibleProfileCoverSpace B κ ℓ i) ≤
      withinProfileBound κ := by
  classical
  exact PallLean.Paper93.profileSubspace_compiledBasis_finrank_le_withinProfileBound
    B κ ℓ ((admissibleProfileCoverEnum κ i).val)
    ((admissibleProfileCoverEnum κ i).property)

/-- Step (b), isolated as the single remaining classifier statement.  Expanding
`iterDerivList S` of the allocated product by Leibniz should classify every
summand into one admissible profile space; linearity then gives this membership
in the finite `iSup` cover. -/
def AllocatedDerivativeProductAdmissibleProfileHrow
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat) : Prop :=
  ∀ (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
    S.length = κ →
    m.totalDegree ≤ ℓ →
    m.vars ⊆ S.toFinset →
    isBlockAdmissible B S →
    m * iterDerivList S
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc) ∈
      ⨆ i : Fin (admissibleProfileCoverCard κ),
        admissibleProfileCoverSpace B κ ℓ i



/-- Local factors whose product is the allocated derivative product. -/
noncomputable abbrev allocatedDerivativeLocalFactors
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ :=
  fun i => iterDerivList (alloc i)
    (piPlusBooleanProjectedTransformedConstraintFactors
      M n hn2 htb hns D)[i.val]

/-- The allocated derivative product is exactly the product of its allocated
local factors. -/
theorem piPlusBooleanProjectedAllocatedDerivativeProduct_eq_prod_localFactors
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars)) :
    piPlusBooleanProjectedAllocatedDerivativeProduct M n hn2 htb hns D alloc =
      Finset.univ.prod (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc) := by
  rfl

/-- Multiplication by a fixed left factor transports span membership to the
span of multiplied generators. -/
theorem mul_mem_span_image_of_mem_span {N : Nat}
    (m : MvPolynomial (Fin N) ℚ) (A : Set (MvPolynomial (Fin N) ℚ))
    {p : MvPolynomial (Fin N) ℚ}
    (hp : p ∈ Submodule.span ℚ A) :
    m * p ∈ Submodule.span ℚ ((fun q => m * q) '' A) := by
  classical
  refine Submodule.span_induction
    (s := A) (p := fun x _hx => m * x ∈ Submodule.span ℚ ((fun q => m * q) '' A))
    ?mem ?zero ?add ?smul hp
  · intro x hx
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  · simp
  · intro x y _ _ hx hy
    simpa [mul_add] using Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [Algebra.smul_def]
    change m * (C a * x) ∈ Submodule.span ℚ ((fun q => m * q) '' A)
    rw [← mul_assoc, mul_comm m (C a), mul_assoc]
    simpa [Algebra.smul_def] using Submodule.smul_mem
      (Submodule.span ℚ ((fun q => m * q) '' A)) a hx



/-- A profile-local membership classifier for bounded Leibniz summands closes the
`hsummand` obligation: every bounded product-choice generator has a derivative
count profile `h`; admissibility transports `h` into the finite admissible-profile
cover, and the supplied membership places the shifted summand in that cover
component. -/
theorem boundedLeibnizSummandCover_of_profileSubspaceClassifier
    {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ)
    (hSlen : S.length = κ)
    (hclassifier : ∀ (h : ProfileHistogram) (g : MvPolynomial (Fin N) ℚ),
      g ∈ boundedProfileClassifiedSet factors constraintType S h →
      m * g ∈ profileSubspace h
        (fun σ : ConstraintType => PallLean.Paper93.interfaceSpace_compiledBasis B κ ℓ σ)) :
    ∀ g ∈ boundedDistribDerivProds Finset.univ factors S S.length,
      m * g ∈ ⨆ i : Fin (admissibleProfileCoverCard κ),
        admissibleProfileCoverSpace B κ ℓ i := by
  classical
  intro g hg
  have hg_union := (boundedDistribDerivProds_subset_iUnion_bounded
    factors constraintType S) hg
  simp only [Set.mem_iUnion] at hg_union
  rcases hg_union with ⟨h, hg_profile⟩
  have hadmS : ProfileAdmissible S.length h :=
    boundedProfileClassifiedSet_profile_admissible
      factors constraintType S h g hg_profile
  have hadmκ : ProfileAdmissible κ h := by
    simpa [hSlen] using hadmS
  let ap : AdmissibleProfile κ := ⟨h, hadmκ⟩
  let i : Fin (admissibleProfileCoverCard κ) :=
    (Fintype.equivFin (AdmissibleProfile κ)) ap
  have hi : (admissibleProfileCoverEnum κ i).val = h := by
    show ((Fintype.equivFin (AdmissibleProfile κ)).symm
      ((Fintype.equivFin (AdmissibleProfile κ)) ap)).val = h
    simp [ap]
  apply Submodule.mem_iSup_of_mem i
  change m * g ∈ profileSubspace ((admissibleProfileCoverEnum κ i).val)
    (fun σ : ConstraintType => PallLean.Paper93.interfaceSpace_compiledBasis B κ ℓ σ)
  simpa [hi] using hclassifier h g hg_profile

/-- Step-(b) reduction: it is enough to classify every bounded Leibniz summand
`g` of the outer derivative of the allocated local-factor product after the
left shift `m`.  The generic bounded Leibniz theorem then gives the full `hrow`
membership. -/
theorem allocatedDerivativeProduct_hrow_of_boundedLeibnizSummandCover
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
    (_hSlen : S.length = κ)
    (_hmdeg : m.totalDegree ≤ ℓ)
    (_hmvars : m.vars ⊆ S.toFinset)
    (_hadm : isBlockAdmissible B S)
    (hsummand : ∀ g ∈ boundedDistribDerivProds Finset.univ
        (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc) S S.length,
      m * g ∈ ⨆ i : Fin (admissibleProfileCoverCard κ),
        admissibleProfileCoverSpace B κ ℓ i) :
    m * iterDerivList S
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc) ∈
      ⨆ i : Fin (admissibleProfileCoverCard κ),
        admissibleProfileCoverSpace B κ ℓ i := by
  classical
  let A := boundedDistribDerivProds Finset.univ
        (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc) S S.length
  have hLeibniz : iterDerivList S
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc) ∈ Submodule.span ℚ A := by
    simpa [A, piPlusBooleanProjectedAllocatedDerivativeProduct_eq_prod_localFactors]
      using iterDerivList_finset_prod_mem_bounded_span S
        (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc)
  have hmul : m * iterDerivList S
      (piPlusBooleanProjectedAllocatedDerivativeProduct
        M n hn2 htb hns D alloc) ∈
      Submodule.span ℚ ((fun g => m * g) '' A) :=
    mul_mem_span_image_of_mem_span m A hLeibniz
  refine (Submodule.span_le.mpr ?_) hmul
  intro q hq
  rcases hq with ⟨g, hg, rfl⟩
  simpa [A] using hsummand g hg

/-- Uniform Step-(b) reduction to the named `hrow` classifier. -/
theorem allocatedDerivativeProduct_admissibleProfileHrow_of_boundedLeibnizSummandCover
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (hsummand : ∀
      (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible B S →
      ∀ g ∈ boundedDistribDerivProds Finset.univ
          (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc) S S.length,
        m * g ∈ ⨆ i : Fin (admissibleProfileCoverCard κ),
          admissibleProfileCoverSpace B κ ℓ i) :
    AllocatedDerivativeProductAdmissibleProfileHrow
      M n hn2 htb hns D alloc B κ ℓ := by
  intro S m hSlen hmdeg hmvars hadm
  exact allocatedDerivativeProduct_hrow_of_boundedLeibnizSummandCover
    M n hn2 htb hns D alloc B κ ℓ S m hSlen hmdeg hmvars hadm
    (hsummand S m hSlen hmdeg hmvars hadm)

/-- Full allocated-product hrow from a profile-local classifier for every bounded
Leibniz summand of the allocated local-factor product.  This is the narrow final
math seam: prove `hclassifier` using per-factor derivative spans and
`profileProduct_mem_profileSubspace`; the rest of the raw-rank bound is now
formal plumbing. -/
theorem allocatedDerivativeProduct_admissibleProfileHrow_of_profileSubspaceClassifier
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (constraintType : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length → ConstraintType)
    (hclassifier : ∀
      (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible B S →
      ∀ (h : ProfileHistogram) (g : MvPolynomial
          (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
        g ∈ boundedProfileClassifiedSet
          (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc)
          constraintType S h →
        m * g ∈ profileSubspace h
          (fun σ : ConstraintType => PallLean.Paper93.interfaceSpace_compiledBasis B κ ℓ σ)) :
    AllocatedDerivativeProductAdmissibleProfileHrow
      M n hn2 htb hns D alloc B κ ℓ := by
  refine allocatedDerivativeProduct_admissibleProfileHrow_of_boundedLeibnizSummandCover
    M n hn2 htb hns D alloc B κ ℓ ?_
  intro S m hSlen hmdeg hmvars hadm g hg
  exact boundedLeibnizSummandCover_of_profileSubspaceClassifier
    B κ ℓ
    (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc)
    constraintType S m hSlen
    (hclassifier S m hSlen hmdeg hmvars hadm) g hg

/-- Paper-scale version of the profile-local classifier closeout. -/
theorem paperScale_allocatedDerivativeProduct_admissibleProfileHrow_of_profileSubspaceClassifier
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (κ ℓ : Nat)
    (constraintType : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length → ConstraintType)
    (hclassifier : ∀
      (S : List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
      (m : MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition S →
      ∀ (h : ProfileHistogram) (g : MvPolynomial
          (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ),
        g ∈ boundedProfileClassifiedSet
          (allocatedDerivativeLocalFactors M (2 ^ 804) paperScale_ge_two htb hns
            (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc)
          constraintType S h →
        m * g ∈ profileSubspace h
          (fun σ : ConstraintType => PallLean.Paper93.interfaceSpace_compiledBasis
            (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition κ ℓ σ)) :
    AllocatedDerivativeProductAdmissibleProfileHrow
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
      alloc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      κ ℓ := by
  exact allocatedDerivativeProduct_admissibleProfileHrow_of_profileSubspaceClassifier
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    alloc
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ constraintType hclassifier


/-- Step (a)+(c) closeout: once the Step-(b) `hrow` classifier is proved for
the admissible-profile cover, the raw allocated-product rank has the expected
`#admissible_profiles × withinProfileBound κ` budget. -/
theorem allocatedDerivativeProduct_rawRank_le_admissibleProfileCover_of_hrow
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (hrow : AllocatedDerivativeProductAdmissibleProfileHrow
      M n hn2 htb hns D alloc B κ ℓ) :
    rkSPDP B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ≤
      admissibleProfileCoverCard κ * withinProfileBound κ := by
  classical
  haveI : ∀ i : Fin (admissibleProfileCoverCard κ),
      Module.Finite ℚ (admissibleProfileCoverSpace B κ ℓ i) :=
    fun i => admissibleProfileCoverSpace_finite B κ ℓ i
  exact allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows
    M n hn2 htb hns D alloc B κ ℓ
    (admissibleProfileCoverSpace B κ ℓ)
    hrow
    (admissibleProfileCoverSpace_finrank_le_withinProfileBound B κ ℓ)



/-- Direct raw-rank closeout from the profile-local classifier. -/
theorem allocatedDerivativeProduct_rawRank_le_admissibleProfileCover_of_profileSubspaceClassifier
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (D : PiPlusSATBlockCoordinateData M n hn2 htb hns)
    (alloc : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length →
      List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (B : BlockPartition (cook_levin_compilation M n hn2 htb hns).numVars)
    (κ ℓ : Nat)
    (constraintType : Fin (piPlusBooleanProjectedTransformedConstraintFactors
        M n hn2 htb hns D).length → ConstraintType)
    (hclassifier : ∀
      (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
      (m : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible B S →
      ∀ (h : ProfileHistogram) (g : MvPolynomial
          (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ),
        g ∈ boundedProfileClassifiedSet
          (allocatedDerivativeLocalFactors M n hn2 htb hns D alloc)
          constraintType S h →
        m * g ∈ profileSubspace h
          (fun σ : ConstraintType => PallLean.Paper93.interfaceSpace_compiledBasis B κ ℓ σ)) :
    rkSPDP B κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M n hn2 htb hns D alloc) ≤
      admissibleProfileCoverCard κ * withinProfileBound κ := by
  exact allocatedDerivativeProduct_rawRank_le_admissibleProfileCover_of_hrow
    M n hn2 htb hns D alloc B κ ℓ
    (allocatedDerivativeProduct_admissibleProfileHrow_of_profileSubspaceClassifier
      M n hn2 htb hns D alloc B κ ℓ constraintType hclassifier)

/-- Paper-scale specialization of the admissible-profile-cover closeout. -/
theorem paperScale_allocatedDerivativeProduct_rawRank_le_admissibleProfileCover_of_hrow
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (alloc : Fin (cookLevinPiPlusBooleanProjectedTransformedConstraintFactors_paperScale
        M htb hns).length →
      List (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars))
    (κ ℓ : Nat)
    (hrow : AllocatedDerivativeProductAdmissibleProfileHrow
      M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
      alloc
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      κ ℓ) :
    rkSPDP
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        κ ℓ
        (piPlusBooleanProjectedAllocatedDerivativeProduct
          M (2 ^ 804) paperScale_ge_two htb hns
          (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns) alloc) ≤
      admissibleProfileCoverCard κ * withinProfileBound κ := by
  exact allocatedDerivativeProduct_rawRank_le_admissibleProfileCover_of_hrow
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusBlockCoordinateData_paperScale M htb hns)
    alloc
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    κ ℓ hrow

/-! ## Axiom audit anchors -/

#print axioms multilinearize_allocatedDerivativeProduct_eq_normalizedFactorProduct
#print axioms allocatedNormalizedFactorProduct_multilinearizedRank_le_rawAllocatedProductRank
#print axioms rawRank_le_sum_subspaces_of_rawSubspace_le
#print axioms rawRank_le_sum_subspaces_of_generator_rows
#print axioms allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows
#print axioms paperScale_allocatedDerivativeProduct_rawRank_le_profileCover_of_generator_rows
#print axioms boundedLeibnizSummandCover_of_profileSubspaceClassifier
#print axioms allocatedDerivativeProduct_admissibleProfileHrow_of_profileSubspaceClassifier
#print axioms paperScale_allocatedDerivativeProduct_admissibleProfileHrow_of_profileSubspaceClassifier
#print axioms allocatedDerivativeProduct_rawRank_le_admissibleProfileCover_of_profileSubspaceClassifier
#print axioms allocatedDerivativeProduct_hrow_of_boundedLeibnizSummandCover
#print axioms allocatedDerivativeProduct_admissibleProfileHrow_of_boundedLeibnizSummandCover
#print axioms allocatedDerivativeProduct_rawRank_le_admissibleProfileCover_of_hrow
#print axioms paperScale_allocatedDerivativeProduct_rawRank_le_admissibleProfileCover_of_hrow

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
