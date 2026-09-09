import PallLean.MlProjFar
import PallLean.ProductDeriv

/-!
# A concrete binomial minor in the actual SPDP space of a full monomial

For `P = prod_i X_i`, differentiating with respect to a set `S` of distinct
variables leaves exactly the product over its complement.  Different sets
give different squarefree monomials.  Consequently the selected coefficient
matrix is the identity and the repository's actual strict multilinear
blocked SPDP rank is at least `choose n k` for the discrete partition.
The same lower bound holds with any nonnegative shift allowance and in the
inclusive derivative convention.

No linear-independence certificate or rank premise is assumed.  This is an
easy polynomial with a short product presentation, not a lower bound on
general circuit size or a hard-family SAT separation result.

At derivative order `log_2 n`, the rank exceeds `n^d` for every fixed `d`
once `n >= 2^(max 20 (4*(d+1)))`.  This refutes a uniform polynomial upper
bound for this explicit easy family and this global SPDP invariant.  It
does not refute a bound conditional on a hypothetical SAT decider or assert
anything about the existence of such a decider.
-/

namespace GodMoveMonomialMinor

open MvPolynomial SPDP MultilinearSPDP
open scoped BigOperators

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) ℚ

def discreteBlocks (n : ℕ) : BlockPartition n where
  numBlocks := n
  assign := id

noncomputable def fullMonomial (n : ℕ) : Poly n := ∏ i : Fin n, X i

/-- All `k`-subsets, with their actual finite enumeration. -/
abbrev KSubset (n k : ℕ) := ↥((Finset.univ : Finset (Fin n)).powersetCard k)

theorem kSubset_card (n k : ℕ) : Fintype.card (KSubset n k) = Nat.choose n k := by
  simp [KSubset]

theorem kSubset_size {n k : ℕ} (S : KSubset n k) : S.val.card = k :=
  (Finset.mem_powersetCard.mp S.property).2

theorem pderiv_prod_X {n : ℕ} (s : Finset (Fin n)) (i : Fin n) (hi : i ∈ s) :
    pderiv i (∏ j ∈ s, (X j : Poly n)) = ∏ j ∈ s.erase i, (X j : Poly n) := by
  rw [ProductDeriv.pderiv_prod_single hi]
  · simp
  · intro j _ hji
    exact pderiv_X_of_ne hji

theorem iterDerivList_prod_X {n : ℕ} (s : Finset (Fin n))
    (S : List (Fin n)) (hS : S.Nodup) (hSs : ∀ i ∈ S, i ∈ s) :
    iterDerivList S (∏ i ∈ s, (X i : Poly n)) =
      ∏ i ∈ s \ S.toFinset, (X i : Poly n) := by
  induction S generalizing s with
  | nil => simp [iterDerivList]
  | cons i rest ih =>
    have hi : i ∈ s := hSs i (by simp)
    have hnd := (List.nodup_cons.mp hS).2
    have hin := (List.nodup_cons.mp hS).1
    rw [IterDerivHelpers.iterDerivList_cons, pderiv_prod_X s i hi]
    have hrest : ∀ j ∈ rest, j ∈ s.erase i := by
      intro j hj
      exact Finset.mem_erase.mpr ⟨fun h => hin (h ▸ hj), hSs j (by simp [hj])⟩
    rw [ih (s.erase i) hnd hrest]
    congr 1
    ext j
    simp only [List.toFinset_cons, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
    tauto

noncomputable def derivativeRow {n : ℕ} (S : Finset (Fin n)) : Poly n :=
  iterDerivList S.toList (fullMonomial n)

noncomputable def complementaryColumn {n : ℕ} (S : Finset (Fin n)) : Fin n →₀ ℕ :=
  SymmetricPower.tagMonomial (Finset.univ \ S)

theorem derivativeRow_eq_complement_product {n : ℕ} (S : Finset (Fin n)) :
    derivativeRow S = ∏ i ∈ Finset.univ \ S, (X i : Poly n) := by
  unfold derivativeRow fullMonomial
  rw [iterDerivList_prod_X Finset.univ S.toList S.nodup_toList
    (fun _ _ => Finset.mem_univ _)]
  simp

theorem derivativeRow_eq_monomial {n : ℕ} (S : Finset (Fin n)) :
    derivativeRow S = monomial (complementaryColumn S) (1 : ℚ) := by
  rw [derivativeRow_eq_complement_product]
  exact MlProjFar.prod_X_eq_monomial_tag _

theorem complementaryColumn_injective {n : ℕ} :
    Function.Injective (complementaryColumn (n := n)) := by
  intro S T h
  have hd : Finset.univ \ S = Finset.univ \ T :=
    SymmetricPower.tagMonomial_injective h
  ext i
  have hi := Finset.ext_iff.mp hd i
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi
  tauto

/-- The selected coefficient matrix is literally the identity. -/
theorem coefficient_identity {n : ℕ} (S T : Finset (Fin n)) :
    coeff (complementaryColumn S) (derivativeRow T) = if S = T then 1 else 0 := by
  rw [derivativeRow_eq_monomial]
  simp [MvPolynomial.coeff_monomial, complementaryColumn_injective.eq_iff, eq_comm]

theorem coefficient_diagonal {n : ℕ} (S : Finset (Fin n)) :
    coeff (complementaryColumn S) (derivativeRow S) = 1 := by
  simp [coefficient_identity]

theorem coefficient_off_diagonal {n : ℕ} (S T : Finset (Fin n)) (h : S ≠ T) :
    coeff (complementaryColumn S) (derivativeRow T) = 0 := by
  simp [coefficient_identity, h]

theorem derivativeRow_multilinear {n : ℕ} (S : Finset (Fin n)) :
    IsMultilinear (derivativeRow S) := by
  rw [derivativeRow_eq_monomial]
  intro a ha i
  have hcol : a = complementaryColumn S := by
    simpa using support_monomial_subset ha
  rw [hcol]
  exact SymmetricPower.tagMonomial_isMultilinear _ i

theorem derivativeRow_mlProj {n : ℕ} (S : Finset (Fin n)) :
    mlProj (derivativeRow S) = derivativeRow S :=
  mlProj_of_isMultilinear _ (derivativeRow_multilinear S)

theorem discrete_admissible {n : ℕ} (S : Finset (Fin n)) :
    isBlockAdmissible (discreteBlocks n) S.toList := by
  constructor
  · exact S.nodup_toList
  · intro b
    simpa [discreteBlocks, List.count_eq_length_filter, beq_iff_eq] using
      (List.nodup_iff_count_le_one.mp S.nodup_toList b)

theorem derivativeRow_mem_strict {n k : ℕ} (S : KSubset n k) (ell : ℕ) :
    derivativeRow S.val ∈ mlBlockedSpdpSubspace (discreteBlocks n) k ell (fullMonomial n) := by
  apply Submodule.subset_span
  refine ⟨S.val.toList, (1 : Poly n), ?_, by simp, by simp,
    discrete_admissible S.val, ?_⟩
  · simpa using kSubset_size S
  · simpa only [one_mul] using (derivativeRow_mlProj S.val).symm

theorem derivativeRows_linearIndependent (n k : ℕ) :
    LinearIndependent ℚ (fun S : KSubset n k => derivativeRow S.val) := by
  have hli := (MvPolynomial.basisMonomials (Fin n) ℚ).linearIndependent.comp
    (fun S : KSubset n k => complementaryColumn S.val)
    (complementaryColumn_injective.comp Subtype.val_injective)
  simpa only [derivativeRow_eq_monomial] using hli

/-- A binomial lower bound in the repository's actual strict SPDP space,
including the zero-shift case. -/
theorem choose_le_strict_rank (n k ell : ℕ) :
    Nat.choose n k ≤ mlBlockedSpdpRank (discreteBlocks n) k ell (fullMonomial n) := by
  let rows : KSubset n k → mlBlockedSpdpSubspace (discreteBlocks n) k ell (fullMonomial n) :=
    fun S => ⟨derivativeRow S.val, derivativeRow_mem_strict S ell⟩
  have hli : LinearIndependent ℚ rows := by
    apply LinearIndependent.of_comp (mlBlockedSpdpSubspace (discreteBlocks n) k ell
      (fullMonomial n)).subtype
    exact derivativeRows_linearIndependent n k
  have hc := hli.fintype_card_le_finrank
  simpa only [kSubset_card, mlBlockedSpdpRank] using hc

theorem choose_le_inclusive_rank (n k ell : ℕ) :
    Nat.choose n k ≤ mlBlockedSpdpRankInc (discreteBlocks n) k ell (fullMonomial n) := by
  exact (choose_le_strict_rank n k ell).trans
    (Submodule.finrank_mono (mlBlockedSpdpSubspace_le_inc (discreteBlocks n) k ell (fullMonomial n)))

/-! ## Explicit superpolynomial calibration at logarithmic derivative order -/

theorem npow_lt_choose_log (n d : ℕ)
    (hn : 2 ^ (max 20 (4 * (d + 1))) ≤ n) :
    n ^ d < Nat.choose n (Nat.log 2 n) := by
  have hn20 : 2 ^ 20 ≤ n :=
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_left _ _)).trans hn
  have hnpow : 2 ^ (4 * (d + 1)) ≤ n :=
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_max_right _ _)).trans hn
  have hlog : 4 * (d + 1) ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by decide : 1 < 2) hnpow
  have hexp : d < Nat.log 2 n / 4 := by omega
  have hn1 : 1 < n := (by norm_num : 1 < (2 : ℕ) ^ 20).trans_le hn20
  calc
    n ^ d < n ^ (Nat.log 2 n / 4) := Nat.pow_lt_pow_right hn1 hexp
    _ ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
      BinomialBound.binomial_lower_bound_concrete n hn20
    _ ≤ Nat.choose n (Nat.log 2 n) :=
      Nat.choose_mono _ (Nat.div_le_self n 30)

theorem npow_lt_strict_rank (n d ell : ℕ)
    (hn : 2 ^ (max 20 (4 * (d + 1))) ≤ n) :
    n ^ d < mlBlockedSpdpRank (discreteBlocks n) (Nat.log 2 n) ell (fullMonomial n) :=
  (npow_lt_choose_log n d hn).trans_le (choose_le_strict_rank n (Nat.log 2 n) ell)

theorem npow_lt_inclusive_rank (n d ell : ℕ)
    (hn : 2 ^ (max 20 (4 * (d + 1))) ≤ n) :
    n ^ d < mlBlockedSpdpRankInc (discreteBlocks n) (Nat.log 2 n) ell (fullMonomial n) :=
  (npow_lt_choose_log n d hn).trans_le (choose_le_inclusive_rank n (Nat.log 2 n) ell)

set_option exponentiation.threshold 1000 in
theorem npow200_lt_strict_rank (n ell : ℕ) (hn : 2 ^ 804 ≤ n) :
    n ^ 200 < mlBlockedSpdpRank (discreteBlocks n) (Nat.log 2 n) ell (fullMonomial n) :=
  npow_lt_strict_rank n 200 ell hn

set_option exponentiation.threshold 1000 in
theorem npow200_lt_inclusive_rank (n ell : ℕ) (hn : 2 ^ 804 ≤ n) :
    n ^ 200 < mlBlockedSpdpRankInc (discreteBlocks n) (Nat.log 2 n) ell (fullMonomial n) :=
  npow_lt_inclusive_rank n 200 ell hn

/-- No eventual bound `C * n^d` holds for the zero-shift strict rank of this
explicit family.  There is no machine or SAT-decider hypothesis here. -/
theorem no_eventual_polynomial_strict_bound :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0,
      mlBlockedSpdpRank (discreteBlocks n) (Nat.log 2 n) 0 (fullMonomial n) ≤ C * n ^ d := by
  rintro ⟨C, d, n0, hbound⟩
  let n := max (max C n0) (2 ^ (max 20 (4 * (d + 1 + 1))))
  have hn0 : n0 ≤ n := (le_max_right C n0).trans (le_max_left _ _)
  have hnC : C ≤ n := (le_max_left C n0).trans (le_max_left _ _)
  have hnlarge : 2 ^ (max 20 (4 * (d + 1 + 1))) ≤ n := le_max_right _ _
  have hlow := npow_lt_strict_rank n (d + 1) 0 hnlarge
  have hup : C * n ^ d ≤ n ^ (d + 1) := by
    rw [pow_succ, mul_comm (n ^ d) n]
    exact Nat.mul_le_mul_right _ hnC
  exact (not_le_of_gt hlow) ((hbound n hn0).trans hup)

/-- The same explicit family also excludes an eventual polynomial bound for
the inclusive rank; the strict rows are included in its row space. -/
theorem no_eventual_polynomial_inclusive_bound :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0,
      mlBlockedSpdpRankInc (discreteBlocks n) (Nat.log 2 n) 0 (fullMonomial n) ≤ C * n ^ d := by
  rintro ⟨C, d, n0, hbound⟩
  apply no_eventual_polynomial_strict_bound
  refine ⟨C, d, n0, fun n hn => ?_⟩
  exact (Submodule.finrank_mono
    (mlBlockedSpdpSubspace_le_inc (discreteBlocks n) (Nat.log 2 n) 0 (fullMonomial n))).trans
    (hbound n hn)

/-- Even allowing any fixed shift budget, no uniform polynomial rank bound
holds for this concrete family. -/
theorem no_uniform_polynomial_rank_bound (C d ell : ℕ) :
    ¬ ∀ n, mlBlockedSpdpRank (discreteBlocks n) (Nat.log 2 n) ell (fullMonomial n) ≤
      C * n ^ d := by
  intro hbound
  apply no_eventual_polynomial_strict_bound
  refine ⟨C, d, 0, fun n _ => ?_⟩
  exact (mlBlockedSpdpRank_mono_ell (discreteBlocks n) (Nat.log 2 n)
    (Nat.zero_le ell) (fullMonomial n)).trans (hbound n)

theorem no_uniform_polynomial_inclusive_rank_bound (C d ell : ℕ) :
    ¬ ∀ n, mlBlockedSpdpRankInc (discreteBlocks n) (Nat.log 2 n) ell (fullMonomial n) ≤
      C * n ^ d := by
  intro hbound
  apply no_uniform_polynomial_rank_bound C d ell
  intro n
  exact (Submodule.finrank_mono
    (mlBlockedSpdpSubspace_le_inc (discreteBlocks n) (Nat.log 2 n) ell (fullMonomial n))).trans
    (hbound n)

end GodMoveMonomialMinor

#print axioms GodMoveMonomialMinor.iterDerivList_prod_X
#print axioms GodMoveMonomialMinor.coefficient_identity
#print axioms GodMoveMonomialMinor.derivativeRows_linearIndependent
#print axioms GodMoveMonomialMinor.choose_le_strict_rank
#print axioms GodMoveMonomialMinor.choose_le_inclusive_rank
#print axioms GodMoveMonomialMinor.npow_lt_choose_log
#print axioms GodMoveMonomialMinor.npow_lt_strict_rank
#print axioms GodMoveMonomialMinor.npow_lt_inclusive_rank
#print axioms GodMoveMonomialMinor.npow200_lt_strict_rank
#print axioms GodMoveMonomialMinor.no_eventual_polynomial_strict_bound
#print axioms GodMoveMonomialMinor.no_eventual_polynomial_inclusive_bound
#print axioms GodMoveMonomialMinor.no_uniform_polynomial_rank_bound
#print axioms GodMoveMonomialMinor.no_uniform_polynomial_inclusive_rank_bound
