import PallLean.Paper93.DeepMath.PathB.ZeroProfileShiftSpanProgress

/-!
# Zero-profile support-cardinality bounds

This file advances the cardinality side of the zero-profile shifted-span
blocker isolated in `ZeroProfileShiftSpanProgress`.

The existing blocker reduces the zero-profile common-span statement to

`zeroProfileShiftSupportBasisCardBound (Nat.log 2 n) factors ≤
  withinProfileBound (Nat.log 2 n)`.

Here we prove kernel-checked cardinal estimates for that concrete bound and
package the exact remaining arithmetic side conditions.  The key reduction is
that each support term only needs the elementary inequality

`|(T ∪ baseVars)| ≤ |T| + |baseVars|`.
-/

namespace PallLean
namespace Paper93
namespace DeepMath
namespace PathB

open MvPolynomial SymmetricPowerBound TuringMachine PaperFaithfulSeparation
open WithinProfileBound MultilinearSPDP SPDP
open scoped BigOperators

attribute [local instance] Classical.dec

/-- The finite family of admissible shift supports used by the zero-profile
support basis. -/
noncomputable def zeroProfileShiftSupportSetFamily (n κ : ℕ) :
    Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powerset.filter
    (fun T : Finset (Fin n) => T.card ≤ κ)

/-- Cardinality of the admissible shift-support family. -/
noncomputable def zeroProfileShiftSupportSetCount (n κ : ℕ) : ℕ :=
  (zeroProfileShiftSupportSetFamily n κ).card

/-- Sum bound obtained from replacing `|(T ∪ baseVars)|` by
`|T| + |baseVars|` termwise. -/
noncomputable def zeroProfileSupportCardSumBound {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ) : ℕ :=
  (zeroProfileShiftSupportSetFamily n κ).sum
    (fun T => 2 ^ (T.card + (zeroProfileBaseProductVars factors).card))

/-- Variant of `zeroProfileSupportCardSumBound` using an external bound `b` for
`zeroProfileBaseProductVars.card`. -/
noncomputable def zeroProfileSupportCardSumBoundOfBaseCard
    (n κ b : ℕ) : ℕ :=
  (zeroProfileShiftSupportSetFamily n κ).sum
    (fun T : Finset (Fin n) => 2 ^ (T.card + b))

/-- Exact finite-sum arithmetic side condition left after the union-cardinality
estimate. -/
def ZeroProfileSupportCardSumSideCondition {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ) : Prop :=
  zeroProfileSupportCardSumBound κ factors ≤ withinProfileBound κ

/-- External-base-cardinality version of the remaining arithmetic side
condition. -/
def ZeroProfileSupportBaseCardSideCondition {n L : ℕ}
    (κ b : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ) : Prop :=
  (zeroProfileBaseProductVars factors).card ≤ b ∧
    zeroProfileSupportCardSumBoundOfBaseCard n κ b ≤ withinProfileBound κ

/-- The base-product variables are always a subset of the ambient variable set. -/
theorem zeroProfileBaseProductVars_card_le_univ {n L : ℕ}
    (factors : Fin L → MvPolynomial (Fin n) ℚ) :
    (zeroProfileBaseProductVars factors).card ≤ n := by
  simpa using
    (Finset.card_le_card
      (Finset.subset_univ (zeroProfileBaseProductVars factors)))

/-- Termwise support-cardinality estimate for one admissible shift support. -/
theorem zeroProfile_shift_support_term_le_card_add_base {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (T : Finset (Fin n))
    (_hT : T ∈ zeroProfileShiftSupportSetFamily n κ) :
    2 ^ (T ∪ zeroProfileBaseProductVars factors).card ≤
      2 ^ (T.card + (zeroProfileBaseProductVars factors).card) := by
  exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
    (Finset.card_union_le T (zeroProfileBaseProductVars factors))

/-- The concrete support-basis cardinal bound is at most the exact finite-sum
bound involving `zeroProfileBaseProductVars.card`. -/
theorem zeroProfileShiftSupportBasisCardBound_le_supportCardSumBound {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ) :
    zeroProfileShiftSupportBasisCardBound κ factors ≤
      zeroProfileSupportCardSumBound κ factors := by
  unfold zeroProfileShiftSupportBasisCardBound zeroProfileSupportCardSumBound
    zeroProfileShiftSupportSetFamily
  apply Finset.sum_le_sum
  intro T hT
  exact zeroProfile_shift_support_term_le_card_add_base κ factors T (by
    simpa [zeroProfileShiftSupportSetFamily] using hT)

/-- If the base product uses at most `b` variables, the exact finite-sum bound
can be weakened to the same sum with `b` in place of the actual base-cardinality. -/
theorem zeroProfileSupportCardSumBound_le_of_base_card_le {n L : ℕ}
    (κ b : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hbase : (zeroProfileBaseProductVars factors).card ≤ b) :
    zeroProfileSupportCardSumBound κ factors ≤
      zeroProfileSupportCardSumBoundOfBaseCard n κ b := by
  unfold zeroProfileSupportCardSumBound zeroProfileSupportCardSumBoundOfBaseCard
  apply Finset.sum_le_sum
  intro T _hT
  exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
    (Nat.add_le_add_left hbase T.card)

/-- Combined support-basis estimate from an external base-variable cardinality
bound. -/
theorem zeroProfileShiftSupportBasisCardBound_le_sumBoundOfBaseCard {n L : ℕ}
    (κ b : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hbase : (zeroProfileBaseProductVars factors).card ≤ b) :
    zeroProfileShiftSupportBasisCardBound κ factors ≤
      zeroProfileSupportCardSumBoundOfBaseCard n κ b :=
  (zeroProfileShiftSupportBasisCardBound_le_supportCardSumBound κ factors).trans
    (zeroProfileSupportCardSumBound_le_of_base_card_le κ b factors hbase)

/-- A coarser but compact estimate: the external-base-cardinality finite sum is
bounded by the number of shift supports times the largest term. -/
theorem zeroProfileSupportCardSumBoundOfBaseCard_le_count_mul_pow
    (n κ b : ℕ) :
    zeroProfileSupportCardSumBoundOfBaseCard n κ b ≤
      zeroProfileShiftSupportSetCount n κ * 2 ^ (κ + b) := by
  unfold zeroProfileSupportCardSumBoundOfBaseCard
    zeroProfileShiftSupportSetCount zeroProfileShiftSupportSetFamily
  let A : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powerset.filter
      (fun T : Finset (Fin n) => T.card ≤ κ)
  change A.sum (fun T : Finset (Fin n) => 2 ^ (T.card + b)) ≤
    A.card * 2 ^ (κ + b)
  calc
    A.sum (fun T : Finset (Fin n) => 2 ^ (T.card + b))
        ≤ A.sum (fun _T : Finset (Fin n) => 2 ^ (κ + b)) := by
          apply Finset.sum_le_sum
          intro T hT
          have hT_card : T.card ≤ κ := (Finset.mem_filter.mp hT).2
          exact Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
            (Nat.add_le_add_right hT_card b)
    _ = A.card * 2 ^ (κ + b) := by
          simp

/-- The admissible shift-support family is a subfamily of the full powerset. -/
theorem zeroProfileShiftSupportSetCount_le_powerset_card
    (n κ : ℕ) :
    zeroProfileShiftSupportSetCount n κ ≤
      ((Finset.univ : Finset (Fin n)).powerset).card := by
  unfold zeroProfileShiftSupportSetCount zeroProfileShiftSupportSetFamily
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Coarse cardinality bound for admissible shift supports. -/
theorem zeroProfileShiftSupportSetCount_le_pow
    (n κ : ℕ) :
    zeroProfileShiftSupportSetCount n κ ≤ 2 ^ n := by
  calc
    zeroProfileShiftSupportSetCount n κ
        ≤ ((Finset.univ : Finset (Fin n)).powerset).card :=
          zeroProfileShiftSupportSetCount_le_powerset_card n κ
    _ = 2 ^ n := by
          simp

/-- If `κ ≥ 1`, every singleton ambient variable support is one of the
admissible zero-profile shift supports. -/
theorem zeroProfileShiftSupportSetCount_ge_ambient_of_one_le
    (n κ : ℕ) (hκ : 1 ≤ κ) :
    n ≤ zeroProfileShiftSupportSetCount n κ := by
  classical
  let singletons : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).image
      (fun i => ({i} : Finset (Fin n)))
  have hsingle_card : singletons.card = n := by
    calc
      singletons.card = (Finset.univ : Finset (Fin n)).card := by
        unfold singletons
        apply Finset.card_image_of_injective
        intro a b h
        have ha : a ∈ ((fun i => ({i} : Finset (Fin n))) a) := by simp
        rw [h] at ha
        simpa using ha
      _ = n := by simp
  have hsub : singletons ⊆ zeroProfileShiftSupportSetFamily n κ := by
    intro T hT
    simp only [singletons, Finset.mem_image, Finset.mem_univ, true_and] at hT
    rcases hT with ⟨i, rfl⟩
    unfold zeroProfileShiftSupportSetFamily
    simp [hκ]
  calc
    n = singletons.card := hsingle_card.symm
    _ ≤ (zeroProfileShiftSupportSetFamily n κ).card := Finset.card_le_card hsub
    _ = zeroProfileShiftSupportSetCount n κ := rfl

/-- The exact support-cardinality finite sum is at least the number of
admissible shift supports: every summand is a positive power of `2`. -/
theorem zeroProfileShiftSupportSetCount_le_supportCardSumBound {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ) :
    zeroProfileShiftSupportSetCount n κ ≤
      zeroProfileSupportCardSumBound κ factors := by
  unfold zeroProfileShiftSupportSetCount zeroProfileSupportCardSumBound
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro T _hT
  exact Nat.one_le_pow _ _ (by norm_num : 0 < 2)

/-- The concrete support-basis cardinality bound is already at least the
number of admissible shift supports: every summand is a positive power of
`2`. -/
theorem zeroProfileShiftSupportSetCount_le_supportBasisCardBound {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ) :
    zeroProfileShiftSupportSetCount n κ ≤
      zeroProfileShiftSupportBasisCardBound κ factors := by
  unfold zeroProfileShiftSupportSetCount zeroProfileShiftSupportSetFamily
    zeroProfileShiftSupportBasisCardBound
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro T _hT
  exact Nat.one_le_pow _ _ (by norm_num : 0 < 2)

/-- Consequently, for `κ ≥ 1`, the exact finite-sum side condition already
has ambient-size cost: it is at least `n`, before any Cook-Levin base-product
variables are counted. -/
theorem zeroProfileSupportCardSumBound_ge_ambient_of_one_le {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hκ : 1 ≤ κ) :
    n ≤ zeroProfileSupportCardSumBound κ factors :=
  (zeroProfileShiftSupportSetCount_ge_ambient_of_one_le n κ hκ).trans
    (zeroProfileShiftSupportSetCount_le_supportCardSumBound κ factors)

/-- The support-basis cardinality bound itself has ambient-size cost as soon
as singleton shifts are admissible. -/
theorem zeroProfileShiftSupportBasisCardBound_ge_ambient_of_one_le {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hκ : 1 ≤ κ) :
    n ≤ zeroProfileShiftSupportBasisCardBound κ factors :=
  (zeroProfileShiftSupportSetCount_ge_ambient_of_one_le n κ hκ).trans
    (zeroProfileShiftSupportSetCount_le_supportBasisCardBound κ factors)

/-- The external-base-cardinality finite sum has the same ambient-size lower
bound: singleton shift supports alone already contribute at least `n`. -/
theorem zeroProfileSupportCardSumBoundOfBaseCard_ge_ambient_of_one_le
    (n κ b : ℕ) (hκ : 1 ≤ κ) :
    n ≤ zeroProfileSupportCardSumBoundOfBaseCard n κ b := by
  unfold zeroProfileSupportCardSumBoundOfBaseCard
  calc
    n ≤ zeroProfileShiftSupportSetCount n κ :=
      zeroProfileShiftSupportSetCount_ge_ambient_of_one_le n κ hκ
    _ ≤ (zeroProfileShiftSupportSetFamily n κ).sum
        (fun T : Finset (Fin n) => 2 ^ (T.card + b)) := by
          unfold zeroProfileShiftSupportSetCount
          rw [Finset.card_eq_sum_ones]
          apply Finset.sum_le_sum
          intro T _hT
          exact Nat.one_le_pow _ _ (by norm_num : 0 < 2)

/-- The exact finite-sum side condition implies the ambient-size inequality
`n ≤ withinProfileBound κ`.  This is the key diagnostic obstruction: the
finite-sum support route is already too large when the ambient variable count
exceeds the within-profile polynomial budget. -/
theorem ambient_le_withinProfileBound_of_zeroProfileSupportCardSumSideCondition
    {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hκ : 1 ≤ κ)
    (hside : ZeroProfileSupportCardSumSideCondition κ factors) :
    n ≤ withinProfileBound κ :=
  (zeroProfileSupportCardSumBound_ge_ambient_of_one_le κ factors hκ).trans
    hside

/-- Any proof that the support-basis cardinality bound fits within the
within-profile budget already implies the ambient-size inequality
`n ≤ withinProfileBound κ`. -/
theorem ambient_le_withinProfileBound_of_zeroProfileShiftSupportBasisCardBound_le
    {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hκ : 1 ≤ κ)
    (hbound : zeroProfileShiftSupportBasisCardBound κ factors ≤
      withinProfileBound κ) :
    n ≤ withinProfileBound κ :=
  (zeroProfileShiftSupportBasisCardBound_ge_ambient_of_one_le κ factors hκ).trans
    hbound

/-- If the ambient dimension already exceeds the within-profile budget, the
exact finite-sum support-cardinality side condition is impossible. -/
theorem not_zeroProfileSupportCardSumSideCondition_of_withinProfileBound_lt_ambient
    {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hκ : 1 ≤ κ)
    (hlt : withinProfileBound κ < n) :
    ¬ ZeroProfileSupportCardSumSideCondition κ factors := by
  intro hside
  exact (not_le_of_gt hlt)
    (ambient_le_withinProfileBound_of_zeroProfileSupportCardSumSideCondition
      κ factors hκ hside)

/-- External-base-cardinality side conditions have the same ambient-size
obstruction. -/
theorem ambient_le_withinProfileBound_of_zeroProfileSupportBaseCardSideCondition
    {n L : ℕ}
    (κ b : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hκ : 1 ≤ κ)
    (hside : ZeroProfileSupportBaseCardSideCondition κ b factors) :
    n ≤ withinProfileBound κ :=
  (zeroProfileSupportCardSumBoundOfBaseCard_ge_ambient_of_one_le n κ b hκ).trans
    hside.2

/-- If the ambient dimension already exceeds the within-profile budget, the
external-base-cardinality support side condition is impossible as well. -/
theorem not_zeroProfileSupportBaseCardSideCondition_of_withinProfileBound_lt_ambient
    {n L : ℕ}
    (κ b : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hκ : 1 ≤ κ)
    (hlt : withinProfileBound κ < n) :
    ¬ ZeroProfileSupportBaseCardSideCondition κ b factors := by
  intro hside
  exact (not_le_of_gt hlt)
    (ambient_le_withinProfileBound_of_zeroProfileSupportBaseCardSideCondition
      κ b factors hκ hside)

/-- Coarser closed-form version of the external-base-cardinality finite-sum
estimate. -/
theorem zeroProfileSupportCardSumBoundOfBaseCard_le_univ_pow_mul
    (n κ b : ℕ) :
    zeroProfileSupportCardSumBoundOfBaseCard n κ b ≤
      2 ^ n * 2 ^ (κ + b) :=
  (zeroProfileSupportCardSumBoundOfBaseCard_le_count_mul_pow n κ b).trans
    (Nat.mul_le_mul_right (2 ^ (κ + b))
      (zeroProfileShiftSupportSetCount_le_pow n κ))

/-- Coarse support-basis estimate from an external bound on the base-product
variables. -/
theorem zeroProfileShiftSupportBasisCardBound_le_count_mul_pow_of_base_card_le
    {n L : ℕ}
    (κ b : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hbase : (zeroProfileBaseProductVars factors).card ≤ b) :
    zeroProfileShiftSupportBasisCardBound κ factors ≤
      zeroProfileShiftSupportSetCount n κ * 2 ^ (κ + b) :=
  (zeroProfileShiftSupportBasisCardBound_le_sumBoundOfBaseCard κ b factors hbase).trans
    (zeroProfileSupportCardSumBoundOfBaseCard_le_count_mul_pow n κ b)

/-- Fully closed coarse support-basis estimate from an external bound on the
base-product variables. -/
theorem zeroProfileShiftSupportBasisCardBound_le_univ_pow_mul_of_base_card_le
    {n L : ℕ}
    (κ b : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hbase : (zeroProfileBaseProductVars factors).card ≤ b) :
    zeroProfileShiftSupportBasisCardBound κ factors ≤
      2 ^ n * 2 ^ (κ + b) :=
  (zeroProfileShiftSupportBasisCardBound_le_sumBoundOfBaseCard κ b factors hbase).trans
    (zeroProfileSupportCardSumBoundOfBaseCard_le_univ_pow_mul n κ b)

/-- The exact finite-sum side condition closes the requested
`supportBasisCardBound ≤ withinProfileBound` inequality. -/
theorem zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_sumSideCondition
    {n L : ℕ}
    (κ : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hside : ZeroProfileSupportCardSumSideCondition κ factors) :
    zeroProfileShiftSupportBasisCardBound κ factors ≤ withinProfileBound κ :=
  (zeroProfileShiftSupportBasisCardBound_le_supportCardSumBound κ factors).trans hside

/-- The external-base-cardinality side condition also closes
`supportBasisCardBound ≤ withinProfileBound`. -/
theorem zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_baseCardSideCondition
    {n L : ℕ}
    (κ b : ℕ)
    (factors : Fin L → MvPolynomial (Fin n) ℚ)
    (hside : ZeroProfileSupportBaseCardSideCondition κ b factors) :
    zeroProfileShiftSupportBasisCardBound κ factors ≤ withinProfileBound κ :=
  (zeroProfileShiftSupportBasisCardBound_le_sumBoundOfBaseCard
      κ b factors hside.1).trans hside.2

/-- Cook-Levin instance of the exact remaining finite-sum side condition. -/
def CookLevinZeroProfileSupportCardSumSideCondition
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ZeroProfileSupportCardSumSideCondition (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)

/-- Cook-Levin instance of the external-base-cardinality side condition. -/
def CookLevinZeroProfileSupportBaseCardSideCondition
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (b : ℕ) : Prop :=
  ZeroProfileSupportBaseCardSideCondition (Nat.log 2 n) b
    (fun i => (cookLevinFactorList M n hn htb hns).get i)

/-- Cook-Levin requested cardinal inequality, reduced to the exact finite-sum
arithmetic side condition. -/
theorem cookLevin_zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_sumSideCondition
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hside :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn htb hns) :
    zeroProfileShiftSupportBasisCardBound (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
      ≤ withinProfileBound (Nat.log 2 n) :=
  zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_sumSideCondition
    (Nat.log 2 n)
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    hside

/-- Cook-Levin requested cardinal inequality, reduced to a bound on
`zeroProfileBaseProductVars.card` plus the corresponding exact arithmetic
side condition. -/
theorem cookLevin_zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_baseCardSideCondition
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (b : ℕ)
    (hside :
      CookLevinZeroProfileSupportBaseCardSideCondition M n hn htb hns b) :
    zeroProfileShiftSupportBasisCardBound (Nat.log 2 n)
        (fun i => (cookLevinFactorList M n hn htb hns).get i)
      ≤ withinProfileBound (Nat.log 2 n) :=
  zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_baseCardSideCondition
    (Nat.log 2 n) b
    (fun i => (cookLevinFactorList M n hn htb hns).get i)
    hside

/-- Exact finite-sum side condition closes the zero-profile shifted-span
blocker through the existing support-basis reduction. -/
theorem cookLevinZeroHistogramShiftCommonSpan_of_supportCardSumSideCondition
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hside :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn htb hns) :
    CookLevinZeroHistogramShiftCommonSpan M n hn htb hns :=
  cookLevinZeroHistogramShiftCommonSpan_of_supportBasisCardBound_le
    M n hn htb hns
    (cookLevin_zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_sumSideCondition
      M n hn htb hns hside)

/-- External-base-cardinality side condition closes the zero-profile
shifted-span blocker through the existing support-basis reduction. -/
theorem cookLevinZeroHistogramShiftCommonSpan_of_supportBaseCardSideCondition
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (b : ℕ)
    (hside :
      CookLevinZeroProfileSupportBaseCardSideCondition M n hn htb hns b) :
    CookLevinZeroHistogramShiftCommonSpan M n hn htb hns :=
  cookLevinZeroHistogramShiftCommonSpan_of_supportBasisCardBound_le
    M n hn htb hns
    (cookLevin_zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_baseCardSideCondition
      M n hn htb hns b hside)

/-- Cook-Levin instance of the ambient-size obstruction for the exact
zero-profile support-card finite-sum side condition. -/
theorem ambient_le_withinProfileBound_of_CookLevinZeroProfileSupportCardSumSideCondition
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hside :
      CookLevinZeroProfileSupportCardSumSideCondition M n hn htb hns) :
    n ≤ withinProfileBound (Nat.log 2 n) := by
  have hlog_pos : 0 < Nat.log 2 n := Nat.log_pos (by omega) hn
  exact
    ambient_le_withinProfileBound_of_zeroProfileSupportCardSumSideCondition
      (Nat.log 2 n)
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (Nat.succ_le_of_lt hlog_pos)
      hside

/-- If the Cook-Levin ambient variable count exceeds the within-profile budget,
the exact finite-sum support-cardinality side condition cannot hold. -/
theorem not_CookLevinZeroProfileSupportCardSumSideCondition_of_withinProfileBound_lt_ambient
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hlt : withinProfileBound (Nat.log 2 n) < n) :
    ¬ CookLevinZeroProfileSupportCardSumSideCondition M n hn htb hns := by
  intro hside
  exact (not_le_of_gt hlt)
    (ambient_le_withinProfileBound_of_CookLevinZeroProfileSupportCardSumSideCondition
      M n hn htb hns hside)

/-- Cook-Levin instance of the same obstruction for the external-base-card
variant. -/
theorem ambient_le_withinProfileBound_of_CookLevinZeroProfileSupportBaseCardSideCondition
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (b : ℕ)
    (hside :
      CookLevinZeroProfileSupportBaseCardSideCondition M n hn htb hns b) :
    n ≤ withinProfileBound (Nat.log 2 n) := by
  have hlog_pos : 0 < Nat.log 2 n := Nat.log_pos (by omega) hn
  exact
    ambient_le_withinProfileBound_of_zeroProfileSupportBaseCardSideCondition
      (Nat.log 2 n) b
      (fun i => (cookLevinFactorList M n hn htb hns).get i)
      (Nat.succ_le_of_lt hlog_pos)
      hside

/-- Cook-Levin external-base-card side conditions are also impossible when the
ambient variable count exceeds the within-profile budget. -/
theorem not_CookLevinZeroProfileSupportBaseCardSideCondition_of_withinProfileBound_lt_ambient
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (b : ℕ)
    (hlt : withinProfileBound (Nat.log 2 n) < n) :
    ¬ CookLevinZeroProfileSupportBaseCardSideCondition M n hn htb hns b := by
  intro hside
  exact (not_le_of_gt hlt)
    (ambient_le_withinProfileBound_of_CookLevinZeroProfileSupportBaseCardSideCondition
      M n hn htb hns b hside)

/-! ## Axiom audit anchors -/

#print axioms zeroProfileBaseProductVars_card_le_univ
#print axioms zeroProfileShiftSupportBasisCardBound_le_supportCardSumBound
#print axioms zeroProfileShiftSupportSetCount_le_supportBasisCardBound
#print axioms zeroProfileSupportCardSumBound_le_of_base_card_le
#print axioms zeroProfileSupportCardSumBoundOfBaseCard_le_count_mul_pow
#print axioms zeroProfileShiftSupportSetCount_le_pow
#print axioms zeroProfileShiftSupportSetCount_ge_ambient_of_one_le
#print axioms zeroProfileSupportCardSumBound_ge_ambient_of_one_le
#print axioms zeroProfileShiftSupportBasisCardBound_ge_ambient_of_one_le
#print axioms ambient_le_withinProfileBound_of_zeroProfileSupportCardSumSideCondition
#print axioms ambient_le_withinProfileBound_of_zeroProfileShiftSupportBasisCardBound_le
#print axioms not_zeroProfileSupportCardSumSideCondition_of_withinProfileBound_lt_ambient
#print axioms ambient_le_withinProfileBound_of_CookLevinZeroProfileSupportCardSumSideCondition
#print axioms not_CookLevinZeroProfileSupportCardSumSideCondition_of_withinProfileBound_lt_ambient
#print axioms zeroProfileShiftSupportBasisCardBound_le_univ_pow_mul_of_base_card_le
#print axioms zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_sumSideCondition
#print axioms zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_baseCardSideCondition
#print axioms cookLevin_zeroProfileShiftSupportBasisCardBound_le_withinProfileBound_of_sumSideCondition
#print axioms cookLevinZeroHistogramShiftCommonSpan_of_supportCardSumSideCondition
#print axioms cookLevinZeroHistogramShiftCommonSpan_of_supportBaseCardSideCondition

end PathB
end DeepMath
end Paper93
end PallLean
