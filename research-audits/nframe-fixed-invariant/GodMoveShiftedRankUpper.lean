import GodMoveMonomialMinor

/-!
# A finite upper bound for the actual strict shifted-derivative rank

At derivative order `k`, a row is determined by a `k`-subset and a
squarefree shift supported on that subset. A shift containing a square is
annihilated by multilinear projection, regardless of the source polynomial.
Thus, for every source and partition, the strict SPDP rank is at most
`choose n k * sum_(j <= min k ell) choose k j`, and therefore at most
`choose n k * 2^k <= (2*n)^k`.

The proof spans the actual row space by that explicit finite family. It
does not assume source multilinearity or a SAT-decider hypothesis. When
the variable count is polynomial in input size and `k` grows logarithmically,
this is a quasipolynomial upper bound, not the requested polynomial runtime
bound. The shift allowance and the repository's restriction of shift
variables to differentiated variables are retained exactly.
-/

namespace GodMoveShiftedRankUpper

open MvPolynomial SPDP MultilinearSPDP
open GodMoveMonomialMinor (KSubset kSubset_size kSubset_card)
open scoped BigOperators

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℚ

/-- Exact number of squarefree shifts available on a `k`-set. -/
def shiftBudget (k ell : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (min k ell + 1), Nat.choose k j

/-- A derivative subset, a legal shift degree, and a shift subset of that degree. -/
abbrev RowIndex (n k ell : ℕ) :=
  Σ S : KSubset n k, Σ j : Fin (min k ell + 1), ↥(S.val.powersetCard j.val)

theorem rowIndex_card (n k ell : ℕ) :
    Fintype.card (RowIndex n k ell) = Nat.choose n k * shiftBudget k ell := by
  classical
  rw [Fintype.card_sigma]
  have hinner (S : KSubset n k) :
      Fintype.card (Σ j : Fin (min k ell + 1), ↥(S.val.powersetCard j.val)) =
        shiftBudget k ell := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe, Finset.card_powersetCard, kSubset_size S]
    exact Fin.sum_univ_eq_sum_range (fun j => Nat.choose k j) _
  simp only [hinner, Finset.sum_const, Finset.card_univ, kSubset_card, nsmul_eq_mul]
  simp

noncomputable def row {n : ℕ} (k ell : ℕ) (p : Poly n)
    (I : RowIndex n k ell) : Poly n :=
  mlProj (monomial (SymmetricPower.tagMonomial I.2.2.val) (1 : ℚ) *
    iterDerivList I.1.val.toList p)

noncomputable def rowSpan {n : ℕ} (k ell : ℕ) (p : Poly n) : Submodule ℚ (Poly n) :=
  Submodule.span ℚ (Set.range (row k ell p))

/-- Multiplication cannot repair a non-squarefree shift before `mlProj`. -/
theorem mlProj_monomial_mul_eq_zero {n : ℕ}
    (a : Fin n →₀ ℕ) (c : ℚ) (p : Poly n) (ha : ¬ Finsupp.IsMultilinear a) :
    mlProj (monomial a c * p) = 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial b d =>
    rw [monomial_mul, mlProj_monomial]
    apply if_neg
    intro hab
    apply ha
    intro i
    have h := hab i
    simp only [Finsupp.add_apply] at h
    omega
  | add p q hp hq =>
    rw [mul_add, mlProj_add, hp, hq, add_zero]

theorem multilinear_exponent_eq_tag {n : ℕ} (a : Fin n →₀ ℕ)
    (ha : Finsupp.IsMultilinear a) : a = SymmetricPower.tagMonomial a.support := by
  ext i
  by_cases hi : i ∈ a.support
  · have hne := Finsupp.mem_support_iff.mp hi
    have hle := ha i
    have hone : a i = 1 := by omega
    simp [SymmetricPower.tagMonomial_apply, hi, hone]
  · simp [SymmetricPower.tagMonomial_apply, hi, Finsupp.notMem_support_iff.mp hi]

theorem multilinear_support_card_le_degree {n : ℕ} (m : Poly n)
    (a : Fin n →₀ ℕ) (hmem : a ∈ m.support) (ha : Finsupp.IsMultilinear a) :
    a.support.card ≤ m.totalDegree := by
  have h := le_totalDegree hmem
  have hsum : (a.sum fun _ e => e) = a.support.card := by
    change (∑ i ∈ a.support, a i) = a.support.card
    have hone : ∀ i ∈ a.support, a i = 1 := by
      intro i hi
      have hne := Finsupp.mem_support_iff.mp hi
      have hle := ha i
      omega
    calc
      (∑ i ∈ a.support, a i) = ∑ _i ∈ a.support, (1 : ℕ) :=
        Finset.sum_congr rfl hone
      _ = a.support.card := by simp
  rwa [hsum] at h

/-- The finite family spans every legal strict row, retaining the actual
shift-degree allowance. -/
theorem strict_subspace_le_rowSpan {n : ℕ}
    (B : BlockPartition n) (k ell : ℕ) (p : Poly n) :
    mlBlockedSpdpSubspace B k ell p ≤ rowSpan k ell p := by
  classical
  apply Submodule.span_le.mpr
  rintro q ⟨S, m, hlen, hdegree, hvars, hadm, rfl⟩
  have hcard : S.toFinset.card = k := by
    rw [List.toFinset_card_of_nodup hadm.1, hlen]
  let D : KSubset n k :=
    ⟨S.toFinset, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩⟩
  have hderiv : iterDerivList S p = iterDerivList D.val.toList p :=
    IterDerivHelpers.iterDerivList_perm (List.toFinset_toList hadm.1).symm p
  rw [hderiv, m.as_sum, Finset.sum_mul]
  change (mlProjHom ℚ) (∑ a ∈ m.support, monomial a (coeff a m) *
    iterDerivList D.val.toList p) ∈ rowSpan k ell p
  rw [map_sum]
  apply Submodule.sum_mem
  intro a hmem
  change mlProj (monomial a (coeff a m) * iterDerivList D.val.toList p) ∈ _
  by_cases ha : Finsupp.IsMultilinear a
  · have hsub : a.support ⊆ D.val := by
      intro i hi
      exact hvars ((mem_vars i).mpr ⟨a, hmem, hi⟩)
    have hdeg : a.support.card ≤ ell :=
      (multilinear_support_card_le_degree m a hmem ha).trans hdegree
    have hsize : a.support.card ≤ k := (Finset.card_le_card hsub).trans hcard.le
    let degree : Fin (min k ell + 1) := ⟨a.support.card, by omega⟩
    let T : ↥(D.val.powersetCard degree.val) :=
      ⟨a.support, Finset.mem_powersetCard.mpr ⟨hsub, rfl⟩⟩
    let I : RowIndex n k ell := ⟨D, degree, T⟩
    have hrow : mlProj (monomial a (1 : ℚ) * iterDerivList D.val.toList p) = row k ell p I := by
      change mlProj (monomial a (1 : ℚ) * iterDerivList D.val.toList p) =
        mlProj (monomial (SymmetricPower.tagMonomial a.support) (1 : ℚ) *
          iterDerivList D.val.toList p)
      rw [← multilinear_exponent_eq_tag a ha]
    rw [show monomial a (coeff a m) = coeff a m • monomial a (1 : ℚ) by
      rw [smul_monomial, smul_eq_mul, mul_one]]
    rw [smul_mul_assoc, mlProj_smul, hrow]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨I, rfl⟩)
  · rw [mlProj_monomial_mul_eq_zero a (coeff a m) _ ha]
    exact Submodule.zero_mem _

theorem rowSpan_finrank_le {n : ℕ} (k ell : ℕ) (p : Poly n) :
    Module.finrank ℚ (rowSpan k ell p) ≤ Nat.choose n k * shiftBudget k ell := by
  classical
  simpa only [rowSpan, rowIndex_card] using
    (finrank_range_le_card (R := ℚ) (row k ell p))

/-- The exact finite-family upper bound; no source multilinearity is required. -/
theorem strict_rank_le_shiftBudget {n : ℕ}
    (B : BlockPartition n) (k ell : ℕ) (p : Poly n) :
    mlBlockedSpdpRank B k ell p ≤ Nat.choose n k * shiftBudget k ell := by
  classical
  letI : Module.Finite ℚ (rowSpan k ell p) :=
    Module.Finite.span_of_finite ℚ (Set.finite_range (row k ell p))
  exact (Submodule.finrank_mono (strict_subspace_le_rowSpan B k ell p)).trans
    (rowSpan_finrank_le k ell p)

theorem shiftBudget_le_two_pow (k ell : ℕ) : shiftBudget k ell ≤ 2 ^ k := by
  rw [← Nat.sum_range_choose k]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ (min_le_left k ell)))
    (fun _ _ _ => Nat.zero_le _)

theorem strict_rank_le_choose_mul_two_pow {n : ℕ}
    (B : BlockPartition n) (k ell : ℕ) (p : Poly n) :
    mlBlockedSpdpRank B k ell p ≤ Nat.choose n k * 2 ^ k :=
  (strict_rank_le_shiftBudget B k ell p).trans
    (Nat.mul_le_mul_left _ (shiftBudget_le_two_pow k ell))

/-- A convenient bound with an exponent explicit in the derivative order. -/
theorem strict_rank_le_two_mul_vars_pow {n : ℕ}
    (B : BlockPartition n) (k ell : ℕ) (p : Poly n) :
    mlBlockedSpdpRank B k ell p ≤ (2 * n) ^ k := by
  calc
    _ ≤ Nat.choose n k * 2 ^ k := strict_rank_le_choose_mul_two_pow B k ell p
    _ ≤ n ^ k * 2 ^ k := Nat.mul_le_mul_right _ (Nat.choose_le_pow n k)
    _ = (2 * n) ^ k := by rw [mul_pow, mul_comm]

/-- Polynomially many variables give a bound whose exponent still grows
linearly with `k`; no fixed polynomial exponent is inferred. -/
theorem strict_rank_le_of_variable_bound {n : ℕ}
    (B : BlockPartition n) (k ell : ℕ) (p : Poly n)
    (input C d : ℕ) (hvars : n ≤ C * (input + 1) ^ d) :
    mlBlockedSpdpRank B k ell p ≤ (2 * C) ^ k * (input + 1) ^ (d * k) := by
  calc
    _ ≤ (2 * n) ^ k := strict_rank_le_two_mul_vars_pow B k ell p
    _ ≤ (2 * (C * (input + 1) ^ d)) ^ k :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hvars) k
    _ = (2 * C) ^ k * (input + 1) ^ (d * k) := by rw [← mul_assoc, mul_pow, ← pow_mul]

end GodMoveShiftedRankUpper

#print axioms GodMoveShiftedRankUpper.rowIndex_card
#print axioms GodMoveShiftedRankUpper.mlProj_monomial_mul_eq_zero
#print axioms GodMoveShiftedRankUpper.strict_subspace_le_rowSpan
#print axioms GodMoveShiftedRankUpper.strict_rank_le_shiftBudget
#print axioms GodMoveShiftedRankUpper.strict_rank_le_choose_mul_two_pow
#print axioms GodMoveShiftedRankUpper.strict_rank_le_two_mul_vars_pow
#print axioms GodMoveShiftedRankUpper.strict_rank_le_of_variable_bound
