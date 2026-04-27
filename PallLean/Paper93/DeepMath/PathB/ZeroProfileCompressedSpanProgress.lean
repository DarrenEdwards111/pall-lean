import PallLean.Paper93.DeepMath.PathB.ZeroProfileNonScalarClosure

/-!
# Zero-profile compressed-span frontier

This file separates the actual zero-profile common-span problem from the
currently too-large support-cardinality enumeration.

The support basis already proves finite-dimensionality of the shifted
base-product span.  The remaining paper-faithful target is therefore exactly
the dimension bound on that compressed span, not the cardinality of the
monomial support enumeration.
-/

namespace PallLean
namespace Paper93
namespace DeepMath
namespace PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP SPDP
open scoped BigOperators

attribute [local instance] Classical.dec

/-- The actual compressed span of the all-zero profile shifted base-product
rows. -/
noncomputable def zeroProfileCompressedShiftSpan {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ (zeroProfileShiftImageSet κ factors)

/-- Budgeted common-span form for the compressed zero-profile shifted image. -/
def ZeroProfileCompressedSpanCommonSpanWithBudget {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (budget : ℕ) : Prop :=
  ∃ G : Finset (MvPolynomial (Fin n) ℚ),
    G.card ≤ budget ∧
    zeroProfileShiftImageSet κ factors ⊆
      Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ))

/-- Exact finrank condition for the compressed zero-profile shifted-image
span.  The finite-dimensionality clause is included for generic use; for the
actual support-basis construction it is proved below. -/
def ZeroProfileCompressedSpanFinrankCondition {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (budget : ℕ) : Prop :=
  Module.Finite ℚ ↥(zeroProfileCompressedShiftSpan κ factors) ∧
    Module.finrank ℚ ↥(zeroProfileCompressedShiftSpan κ factors) ≤ budget

/-- The support-basis containment proves finite-dimensionality of the exact
compressed shifted-image span. -/
theorem zeroProfileCompressedShiftSpan_finite {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ) :
    Module.Finite ℚ ↥(zeroProfileCompressedShiftSpan κ factors) := by
  classical
  have hle :
      zeroProfileCompressedShiftSpan κ factors ≤
        Submodule.span ℚ
          (↑(zeroProfileShiftSupportBasis κ factors) :
            Set (MvPolynomial (Fin n) ℚ)) :=
    zeroProfileShiftImageSpan_le_supportBasis_span κ factors
  haveI hfinite_support :
      Module.Finite ℚ
        ↥(Submodule.span ℚ
          (↑(zeroProfileShiftSupportBasis κ factors) :
            Set (MvPolynomial (Fin n) ℚ))) :=
    Module.Finite.span_of_finite ℚ
      (Finset.finite_toSet (zeroProfileShiftSupportBasis κ factors))
  exact Module.Finite.of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

/-- The exact compressed shifted-image span has dimension no larger than the
existing support-basis cardinality.  This records precisely where the old
support-card route loses information. -/
theorem zeroProfileCompressedShiftSpan_finrank_le_supportBasis_card {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ) :
    Module.finrank ℚ ↥(zeroProfileCompressedShiftSpan κ factors) ≤
      (zeroProfileShiftSupportBasis κ factors).card := by
  classical
  have hle :
      zeroProfileCompressedShiftSpan κ factors ≤
        Submodule.span ℚ
          (↑(zeroProfileShiftSupportBasis κ factors) :
            Set (MvPolynomial (Fin n) ℚ)) :=
    zeroProfileShiftImageSpan_le_supportBasis_span κ factors
  haveI hfinite_compressed :
      Module.Finite ℚ ↥(zeroProfileCompressedShiftSpan κ factors) :=
    zeroProfileCompressedShiftSpan_finite κ factors
  haveI hfinite_support :
      Module.Finite ℚ
        ↥(Submodule.span ℚ
          (↑(zeroProfileShiftSupportBasis κ factors) :
            Set (MvPolynomial (Fin n) ℚ))) :=
    Module.Finite.span_of_finite ℚ
      (Finset.finite_toSet (zeroProfileShiftSupportBasis κ factors))
  calc
    Module.finrank ℚ ↥(zeroProfileCompressedShiftSpan κ factors)
        ≤ Module.finrank ℚ
            ↥(Submodule.span ℚ
              (↑(zeroProfileShiftSupportBasis κ factors) :
                Set (MvPolynomial (Fin n) ℚ))) :=
          Submodule.finrank_mono hle
    _ ≤ (zeroProfileShiftSupportBasis κ factors).card :=
          finrank_span_finset_le_card (zeroProfileShiftSupportBasis κ factors)

/-! ## Compression certificates -/

/-- A concrete ambient compression separates the zero-profile compressed span
when its kernel has zero intersection with that span.  This is the
paper-faithful linear-algebra target: exhibit a small family of linear
observables that is injective on the actual compressed shifted-image span. -/
def ZeroProfileCompressedSpanKernelSeparated {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    {ι : Type}
    (compress :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] (ι → ℚ)) : Prop :=
  ∀ x : ↥(zeroProfileCompressedShiftSpan κ factors), compress x = 0 → x = 0

/-- Kernel-separation is exactly disjointness of the compressed span from the
ambient compression kernel. -/
theorem zeroProfileCompressedSpanKernelSeparated_iff_disjoint_ker {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    {ι : Type}
    (compress :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] (ι → ℚ)) :
    ZeroProfileCompressedSpanKernelSeparated κ factors compress ↔
      Disjoint (zeroProfileCompressedShiftSpan κ factors)
        (LinearMap.ker compress) := by
  classical
  constructor
  · intro hsep
    rw [disjoint_iff, Submodule.eq_bot_iff]
    intro p hp
    have hp_zero :
        (⟨p, hp.1⟩ :
          ↥(zeroProfileCompressedShiftSpan κ factors)) = 0 :=
      hsep ⟨p, hp.1⟩ (by
        simpa [LinearMap.mem_ker] using hp.2)
    exact congrArg
      (fun x : ↥(zeroProfileCompressedShiftSpan κ factors) =>
        (x : MvPolynomial (Fin n) ℚ)) hp_zero
  · intro hdisj x hx
    apply Subtype.ext
    have hbot :
        zeroProfileCompressedShiftSpan κ factors ⊓ LinearMap.ker compress =
          ⊥ := disjoint_iff.mp hdisj
    have hxinf :
        (x : MvPolynomial (Fin n) ℚ) ∈
          zeroProfileCompressedShiftSpan κ factors ⊓ LinearMap.ker compress := by
      exact ⟨x.property, by simpa [LinearMap.mem_ker] using hx⟩
    exact (Submodule.eq_bot_iff _).mp hbot (x : MvPolynomial (Fin n) ℚ) hxinf

/-- If a compression with at most `budget` coordinates separates the exact
compressed span, then the sharp compressed-span finrank condition follows.
This avoids using the cardinality of the explicit support enumeration as the
target. -/
theorem zeroProfileCompressedSpanFinrankCondition_of_kernelSeparated
    {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (budget : ℕ)
    {ι : Type} [Fintype ι]
    (compress :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] (ι → ℚ))
    (hcard : Fintype.card ι ≤ budget)
    (hsep : ZeroProfileCompressedSpanKernelSeparated κ factors compress) :
    ZeroProfileCompressedSpanFinrankCondition κ factors budget := by
  classical
  let U : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
    zeroProfileCompressedShiftSpan κ factors
  have hfinite : Module.Finite ℚ ↥U :=
    zeroProfileCompressedShiftSpan_finite κ factors
  letI : Module.Finite ℚ ↥U := hfinite
  have hinj : Function.Injective (compress.domRestrict U) := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hsep
    have hzero : (compress.domRestrict U) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    simpa [LinearMap.domRestrict_apply] using hzero
  refine ⟨hfinite, ?_⟩
  calc
    Module.finrank ℚ ↥(zeroProfileCompressedShiftSpan κ factors)
        = Module.finrank ℚ ↥U := rfl
    _ ≤ Module.finrank ℚ (ι → ℚ) :=
          LinearMap.finrank_le_finrank_of_injective
            (f := compress.domRestrict U) hinj
    _ = Fintype.card ι := Module.finrank_fintype_fun_eq_card ℚ
    _ ≤ budget := hcard

/-- Disjoint-kernel form of the compression certificate. -/
theorem zeroProfileCompressedSpanFinrankCondition_of_disjoint_ker
    {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (budget : ℕ)
    {ι : Type} [Fintype ι]
    (compress :
      MvPolynomial (Fin n) ℚ →ₗ[ℚ] (ι → ℚ))
    (hcard : Fintype.card ι ≤ budget)
    (hdisj :
      Disjoint (zeroProfileCompressedShiftSpan κ factors)
        (LinearMap.ker compress)) :
    ZeroProfileCompressedSpanFinrankCondition κ factors budget :=
  zeroProfileCompressedSpanFinrankCondition_of_kernelSeparated
    κ factors budget compress hcard
    ((zeroProfileCompressedSpanKernelSeparated_iff_disjoint_ker
      κ factors compress).mpr hdisj)

/-- The remaining compressed-span obligation as a small ambient linear
compression: find at most `budget` linear coordinates whose common kernel is
disjoint from the exact compressed shifted-image span. -/
def ZeroProfileCompressedSpanKernelDisjointCompressionObligation {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (budget : ℕ) : Prop :=
  ∃ ι : Type, ∃ _ : Fintype ι,
    Fintype.card ι ≤ budget ∧
      ∃ compress : MvPolynomial (Fin n) ℚ →ₗ[ℚ] (ι → ℚ),
        Disjoint (zeroProfileCompressedShiftSpan κ factors)
          (LinearMap.ker compress)

/-- The small ambient compression obligation is sufficient for the exact
compressed-span finrank condition. -/
theorem zeroProfileCompressedSpanFinrankCondition_of_kernelDisjointCompressionObligation
    {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (budget : ℕ)
    (hcompress :
      ZeroProfileCompressedSpanKernelDisjointCompressionObligation
        κ factors budget) :
    ZeroProfileCompressedSpanFinrankCondition κ factors budget := by
  rcases hcompress with ⟨ι, hι, hcard, compress, hdisj⟩
  letI : Fintype ι := hι
  exact zeroProfileCompressedSpanFinrankCondition_of_disjoint_ker
    κ factors budget compress hcard hdisj

/-- Intrinsic coordinate-compression version of the exact finrank condition.
This removes the ambient-extension issue and records the pure linear-algebra
equivalence: the compressed span has finrank at most `budget` iff it injects
into a coordinate space with at most `budget` coordinates. -/
def ZeroProfileCompressedSpanIntrinsicCompressionObligation {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (budget : ℕ) : Prop :=
  ∃ ι : Type, ∃ _ : Fintype ι,
    Fintype.card ι ≤ budget ∧
      ∃ compress :
        ↥(zeroProfileCompressedShiftSpan κ factors) →ₗ[ℚ] (ι → ℚ),
        Function.Injective compress

/-- Exact intrinsic compression equivalence for the zero-profile compressed
span. -/
theorem zeroProfileCompressedSpanIntrinsicCompressionObligation_iff_finrankCondition
    {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (budget : ℕ) :
    ZeroProfileCompressedSpanIntrinsicCompressionObligation κ factors budget ↔
      ZeroProfileCompressedSpanFinrankCondition κ factors budget := by
  classical
  constructor
  · rintro ⟨ι, hι, hcard, compress, hinj⟩
    letI : Fintype ι := hι
    have hfinite :
        Module.Finite ℚ ↥(zeroProfileCompressedShiftSpan κ factors) :=
      zeroProfileCompressedShiftSpan_finite κ factors
    letI :
        Module.Finite ℚ ↥(zeroProfileCompressedShiftSpan κ factors) :=
      hfinite
    refine ⟨hfinite, ?_⟩
    calc
      Module.finrank ℚ ↥(zeroProfileCompressedShiftSpan κ factors)
          ≤ Module.finrank ℚ (ι → ℚ) :=
            LinearMap.finrank_le_finrank_of_injective
              (f := compress) hinj
      _ = Fintype.card ι := Module.finrank_fintype_fun_eq_card ℚ
      _ ≤ budget := hcard
  · rintro ⟨hfinite, hfinrank⟩
    let U : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
      zeroProfileCompressedShiftSpan κ factors
    letI : Module.Finite ℚ ↥U := hfinite
    refine ⟨Fin (Module.finrank ℚ ↥U), inferInstance, ?_, ?_⟩
    · simpa using hfinrank
    · let b : Module.Basis (Fin (Module.finrank ℚ ↥U)) ℚ ↥U :=
        Module.finBasis ℚ ↥U
      exact ⟨b.equivFun.toLinearMap, b.equivFun.injective⟩

/-- Generic exact equivalence: a finite common-span witness of size `budget`
exists if and only if the compressed shifted-image span is finite-dimensional
with finrank at most `budget`. -/
theorem zeroProfileCompressedSpanCommonSpanWithBudget_iff_finrankCondition
    {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (budget : ℕ) :
    ZeroProfileCompressedSpanCommonSpanWithBudget κ factors budget ↔
      ZeroProfileCompressedSpanFinrankCondition κ factors budget := by
  classical
  constructor
  · rintro ⟨G, hG_card, hG_span⟩
    have hle :
        zeroProfileCompressedShiftSpan κ factors ≤
          Submodule.span ℚ (↑G : Set (MvPolynomial (Fin n) ℚ)) :=
      Submodule.span_le.mpr hG_span
    haveI hfinite_G :
        Module.Finite ℚ
          ↥(Submodule.span ℚ
            (↑G : Set (MvPolynomial (Fin n) ℚ))) :=
      Module.Finite.span_of_finite ℚ (Finset.finite_toSet G)
    have hfinite_compressed :
        Module.Finite ℚ ↥(zeroProfileCompressedShiftSpan κ factors) :=
      Module.Finite.of_injective (Submodule.inclusion hle)
        (Submodule.inclusion_injective hle)
    letI : Module.Finite ℚ ↥(zeroProfileCompressedShiftSpan κ factors) :=
      hfinite_compressed
    refine ⟨hfinite_compressed, ?_⟩
    calc
      Module.finrank ℚ ↥(zeroProfileCompressedShiftSpan κ factors)
          ≤ Module.finrank ℚ
              ↥(Submodule.span ℚ
                (↑G : Set (MvPolynomial (Fin n) ℚ))) :=
            Submodule.finrank_mono hle
      _ ≤ G.card := finrank_span_finset_le_card G
      _ ≤ budget := hG_card
  · rintro ⟨hfinite_compressed, hfinrank⟩
    let U : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
      zeroProfileCompressedShiftSpan κ factors
    haveI : Module.Finite ℚ ↥U := hfinite_compressed
    rcases finite_submodule_le_span_finset_card_le_finrank U with
      ⟨G, hU_span, hG_card⟩
    refine ⟨G, hG_card.trans hfinrank, ?_⟩
    intro p hp
    exact hU_span (Submodule.subset_span hp)

/-- Cook-Levin instance of the exact compressed-span finrank condition. -/
def CookLevinZeroProfileCompressedSpanFinrankCondition
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ZeroProfileCompressedSpanFinrankCondition (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (withinProfileBound (Nat.log 2 n))

/-- The actual Cook-Levin zero-profile compressed span is finite-dimensional;
only its sharp dimension bound remains open. -/
theorem cookLevinZeroProfileCompressedShiftSpan_finite
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    Module.Finite ℚ
      ↥(zeroProfileCompressedShiftSpan (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)) :=
  zeroProfileCompressedShiftSpan_finite (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)

/-- Exact Cook-Levin frontier: the theorem-level common-span blocker is
equivalent to the sharp finrank bound for the compressed shifted-image span. -/
theorem cookLevinZeroHistogramShiftCommonSpan_iff_compressedSpanFinrankCondition
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    CookLevinZeroHistogramShiftCommonSpan M n hn htb hns ↔
      CookLevinZeroProfileCompressedSpanFinrankCondition M n hn htb hns := by
  simpa [CookLevinZeroHistogramShiftCommonSpan,
    CookLevinZeroProfileCompressedSpanFinrankCondition,
    ZeroProfileCompressedSpanCommonSpanWithBudget] using
    (zeroProfileCompressedSpanCommonSpanWithBudget_iff_finrankCondition
      (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (withinProfileBound (Nat.log 2 n)))

/-- The sharp compressed-span finrank condition closes the existing
zero-profile common-span blocker. -/
theorem cookLevinZeroHistogramShiftCommonSpan_of_compressedSpanFinrankCondition
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcompressed :
      CookLevinZeroProfileCompressedSpanFinrankCondition M n hn htb hns) :
    CookLevinZeroHistogramShiftCommonSpan M n hn htb hns :=
  (cookLevinZeroHistogramShiftCommonSpan_iff_compressedSpanFinrankCondition
    M n hn htb hns).mpr hcompressed

/-- The old support-card sum side condition factors through the sharper
compressed-span finrank condition.  This is a comparison theorem, not a proof
that the support-card sum is the right frontier. -/
theorem cookLevinZeroProfileCompressedSpanFinrankCondition_of_supportCardSumSideCondition
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hside :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn htb hns) :
    CookLevinZeroProfileCompressedSpanFinrankCondition M n hn htb hns :=
  (cookLevinZeroHistogramShiftCommonSpan_iff_compressedSpanFinrankCondition
    M n hn htb hns).mp
    (cookLevinZeroHistogramShiftCommonSpan_of_supportCardSumSideCondition
      M n hn htb hns hside)

/-- Cook-Levin version of the small ambient compression obligation for the
actual zero-profile compressed shifted-image span. -/
def CookLevinZeroProfileCompressedSpanKernelDisjointCompressionObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ZeroProfileCompressedSpanKernelDisjointCompressionObligation (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (withinProfileBound (Nat.log 2 n))

/-- A small kernel-disjoint ambient compression proves the Cook-Levin
zero-profile compressed-span finrank condition. -/
theorem cookLevinZeroProfileCompressedSpanFinrankCondition_of_kernelDisjointCompressionObligation
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcompress :
      CookLevinZeroProfileCompressedSpanKernelDisjointCompressionObligation
        M n hn htb hns) :
    CookLevinZeroProfileCompressedSpanFinrankCondition M n hn htb hns :=
  zeroProfileCompressedSpanFinrankCondition_of_kernelDisjointCompressionObligation
    (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    (withinProfileBound (Nat.log 2 n))
    hcompress

/-- The actual Cook-Levin zero-profile compressed span cannot satisfy a
one-dimensional compressed-span bound.  This is a checked lower-bound/no-go:
the sharp compressed-span target is not the old singleton template target. -/
theorem not_cookLevinZeroProfileCompressedSpanFinrankCondition_budget_one
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    ¬ ZeroProfileCompressedSpanFinrankCondition (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i) 1 := by
  intro hfinrank
  have hcommon :
      ZeroProfileCompressedSpanCommonSpanWithBudget (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i) 1 :=
    (zeroProfileCompressedSpanCommonSpanWithBudget_iff_finrankCondition
      (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      1).mpr hfinrank
  apply not_cookLevinZeroHistogramTemplateShiftCollapse_actual
    M n hn htb hns
  rcases hcommon with ⟨G, hG_card, hG_span⟩
  refine ⟨G, ?_, hG_span⟩
  simpa [profileTemplateBound_zeroProfileHistogram] using hG_card

/-- Equivalent lower-bound form: the actual Cook-Levin zero-profile compressed
span has finrank at least two. -/
theorem cookLevinZeroProfileCompressedShiftSpan_two_le_finrank
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    2 ≤ Module.finrank ℚ
      ↥(zeroProfileCompressedShiftSpan (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)) := by
  by_contra hnot
  have hle_one :
      Module.finrank ℚ
        ↥(zeroProfileCompressedShiftSpan (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn htb hns).get i)) ≤ 1 := by
    omega
  exact not_cookLevinZeroProfileCompressedSpanFinrankCondition_budget_one
    M n hn htb hns
    ⟨cookLevinZeroProfileCompressedShiftSpan_finite M n hn htb hns,
      hle_one⟩

/-! ## Axiom audit anchors -/

#print axioms zeroProfileCompressedShiftSpan_finite
#print axioms zeroProfileCompressedShiftSpan_finrank_le_supportBasis_card
#print axioms zeroProfileCompressedSpanKernelSeparated_iff_disjoint_ker
#print axioms zeroProfileCompressedSpanFinrankCondition_of_kernelSeparated
#print axioms zeroProfileCompressedSpanFinrankCondition_of_disjoint_ker
#print axioms zeroProfileCompressedSpanFinrankCondition_of_kernelDisjointCompressionObligation
#print axioms zeroProfileCompressedSpanIntrinsicCompressionObligation_iff_finrankCondition
#print axioms zeroProfileCompressedSpanCommonSpanWithBudget_iff_finrankCondition
#print axioms cookLevinZeroHistogramShiftCommonSpan_iff_compressedSpanFinrankCondition
#print axioms cookLevinZeroHistogramShiftCommonSpan_of_compressedSpanFinrankCondition
#print axioms cookLevinZeroProfileCompressedSpanFinrankCondition_of_supportCardSumSideCondition
#print axioms cookLevinZeroProfileCompressedSpanFinrankCondition_of_kernelDisjointCompressionObligation
#print axioms not_cookLevinZeroProfileCompressedSpanFinrankCondition_budget_one
#print axioms cookLevinZeroProfileCompressedShiftSpan_two_le_finrank

end PathB
end DeepMath
end Paper93
end PallLean
