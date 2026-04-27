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

/-! ## Axiom audit anchors -/

#print axioms zeroProfileCompressedShiftSpan_finite
#print axioms zeroProfileCompressedShiftSpan_finrank_le_supportBasis_card
#print axioms zeroProfileCompressedSpanCommonSpanWithBudget_iff_finrankCondition
#print axioms cookLevinZeroHistogramShiftCommonSpan_iff_compressedSpanFinrankCondition
#print axioms cookLevinZeroHistogramShiftCommonSpan_of_compressedSpanFinrankCondition
#print axioms cookLevinZeroProfileCompressedSpanFinrankCondition_of_supportCardSumSideCondition

end PathB
end DeepMath
end Paper93
end PallLean
