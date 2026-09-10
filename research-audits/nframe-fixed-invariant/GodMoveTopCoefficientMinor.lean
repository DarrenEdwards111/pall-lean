import GodMoveMonomialMinor

/-!
# A nonzero top multilinear coefficient forces the full binomial minor

Lower-degree terms cannot cancel the complementary coefficient minor of the
full squarefree monomial. This lemma applies to an actual computation's
normalized polynomial once its top coefficient has been derived. It is a
rank statement, not a computational lower bound.
-/

namespace GodMoveTopCoefficientMinor

open MvPolynomial SPDP MultilinearSPDP
open GodMoveMonomialMinor (Poly KSubset complementaryColumn discreteBlocks)
open scoped BigOperators

noncomputable def fullExponent (n : ℕ) : Fin n →₀ ℕ :=
  SymmetricPower.tagMonomial Finset.univ

@[simp] theorem fullExponent_apply (n : ℕ) (i : Fin n) :
    fullExponent n i = 1 := by
  simp [fullExponent, SymmetricPower.tagMonomial_apply]

/-- The coefficient formula includes the exact derivative multiplicity. -/
theorem coeff_pderiv (i : Fin n) (p : Poly n) (v : Fin n →₀ ℕ) :
    coeff v (pderiv i p) = coeff (v + Finsupp.single i 1) p * (v i + 1 : ℕ) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases hai : a i = 0
    · have hne : a ≠ v + Finsupp.single i 1 := by
        intro h
        have := congrArg (fun b => b i) h
        simp only [Finsupp.add_apply, Finsupp.single_eq_same, hai] at this
        omega
      simp [hai, hne]
    · have heq : a - Finsupp.single i 1 = v ↔ a = v + Finsupp.single i 1 := by
        simp only [Finsupp.ext_iff, Finsupp.tsub_apply, Finsupp.single_apply,
          Finsupp.add_apply]
        constructor <;> intro h j <;> specialize h j <;>
          by_cases hij : i = j
        · subst j; simp only [if_true] at *; omega
        · simp only [hij, if_false] at *; omega
        · subst j; simp only [if_true] at *; omega
        · simp only [hij, if_false] at *; omega
      by_cases ha : a = v + Finsupp.single i 1
      · simp [ha]
      · have hn : a - Finsupp.single i 1 ≠ v := fun h => ha (heq.mp h)
        simp [ha, hn]
  | add p q hp hq =>
    simp only [map_add, coeff_add, hp, hq]
    ring

/-- Distinct differentiations give a single source coefficient with its
exact product of multiplicities. -/
theorem coeff_iterDerivList (S : List (Fin n)) (hS : S.Nodup)
    (p : Poly n) (v : Fin n →₀ ℕ) :
    coeff v (iterDerivList S p) =
      coeff (v + SymmetricPower.tagMonomial S.toFinset) p *
        ∏ i ∈ S.toFinset, (v i + 1 : ℕ) := by
  classical
  induction S generalizing p v with
  | nil => simp [iterDerivList, SymmetricPower.tagMonomial]
  | cons i S ih =>
    obtain ⟨hi, hnd⟩ := List.nodup_cons.mp hS
    have hit : i ∉ S.toFinset := by simpa using hi
    rw [IterDerivHelpers.iterDerivList_cons, ih hnd, coeff_pderiv]
    have hv : (v + SymmetricPower.tagMonomial S.toFinset) i = v i := by
      simp [SymmetricPower.tagMonomial_apply, hit]
    have htag : v + SymmetricPower.tagMonomial (i :: S).toFinset =
        (v + SymmetricPower.tagMonomial S.toFinset) + Finsupp.single i 1 := by
      simp only [List.toFinset_cons, SymmetricPower.tagMonomial,
        Finset.sum_insert hit]
      abel
    rw [htag, hv, List.toFinset_cons, Finset.prod_insert hit]
    push_cast
    ring

/-- The actual complementary coefficient matrix is a nonzero scalar times
the identity whenever the source has a nonzero full squarefree coefficient. -/
theorem complementary_coefficient_identity {n k : ℕ}
    (p : Poly n) (hp : IsMultilinear p) (S T : KSubset n k) :
    coeff (complementaryColumn S.val) (iterDerivList T.val.toList p) =
      if S = T then coeff (fullExponent n) p else 0 := by
  classical
  rw [coeff_iterDerivList _ T.val.nodup_toList]
  simp only [Finset.toList_toFinset]
  by_cases hST : S = T
  · subst T
    have hfull : complementaryColumn S.val + SymmetricPower.tagMonomial S.val =
        fullExponent n := by
      ext i
      by_cases hi : i ∈ S.val <;>
        simp [complementaryColumn, SymmetricPower.tagMonomial_apply, hi]
    have hprod : (∏ i ∈ S.val, (complementaryColumn S.val i + 1 : ℕ)) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      simp [complementaryColumn, SymmetricPower.tagMonomial_apply, hi]
    simp [hfull, hprod]
  · have hnsub : ¬ T.val ⊆ S.val := by
      intro h
      apply hST
      apply Subtype.ext
      exact (Finset.eq_of_subset_of_card_le h
        (by rw [GodMoveMonomialMinor.kSubset_size S,
          GodMoveMonomialMinor.kSubset_size T])).symm
    obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp hnsub
    have hzero : coeff (complementaryColumn S.val + SymmetricPower.tagMonomial T.val) p = 0 := by
      by_contra h
      have hle := hp _ (mem_support_iff.mpr h) i
      simp [complementaryColumn, SymmetricPower.tagMonomial_apply, hiS, hiT] at hle
    simp [hzero, hST]

theorem derivativeRows_linearIndependent {n : ℕ} (p : Poly n)
    (hp : IsMultilinear p) (hcoeff : coeff (fullExponent n) p ≠ 0) (k : ℕ) :
    LinearIndependent ℚ (fun S : KSubset n k => iterDerivList S.val.toList p) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc S
  have h := congrArg (coeff (complementaryColumn S.val)) hc
  simp only [coeff_sum, coeff_smul, smul_eq_mul, complementary_coefficient_identity p hp,
    coeff_zero] at h
  have hsum : (∑ T : KSubset n k, c T *
      (if S = T then coeff (fullExponent n) p else 0)) =
      c S * coeff (fullExponent n) p := by simp
  rw [hsum] at h
  exact (mul_eq_zero.mp h).resolve_right hcoeff

/-- The binomial minor lies in the actual strict SPDP space at every shift allowance. -/
theorem choose_le_strict_rank_of_top_coeff {n : ℕ} (p : Poly n)
    (hp : IsMultilinear p) (hcoeff : coeff (fullExponent n) p ≠ 0) (k ell : ℕ) :
    Nat.choose n k ≤ mlBlockedSpdpRank (discreteBlocks n) k ell p := by
  classical
  have hmem (S : KSubset n k) : iterDerivList S.val.toList p ∈
      mlBlockedSpdpSubspace (discreteBlocks n) k ell p := by
    apply Submodule.subset_span
    refine ⟨S.val.toList, 1, ?_, by simp, by simp,
      GodMoveMonomialMinor.discrete_admissible S.val, ?_⟩
    · simpa using GodMoveMonomialMinor.kSubset_size S
    · simpa using (mlProj_of_isMultilinear _
        (isMultilinear_iterDerivList S.val.toList p hp)).symm
  let rows : KSubset n k → mlBlockedSpdpSubspace (discreteBlocks n) k ell p :=
    fun S => ⟨_, hmem S⟩
  have hli : LinearIndependent ℚ rows := by
    apply LinearIndependent.of_comp (mlBlockedSpdpSubspace (discreteBlocks n) k ell p).subtype
    exact derivativeRows_linearIndependent p hp hcoeff k
  simpa only [GodMoveMonomialMinor.kSubset_card, mlBlockedSpdpRank] using
    hli.fintype_card_le_finrank

theorem choose_le_inclusive_rank_of_top_coeff {n : ℕ} (p : Poly n)
    (hp : IsMultilinear p) (hcoeff : coeff (fullExponent n) p ≠ 0) (k ell : ℕ) :
    Nat.choose n k ≤ mlBlockedSpdpRankInc (discreteBlocks n) k ell p :=
  (choose_le_strict_rank_of_top_coeff p hp hcoeff k ell).trans
    (Submodule.finrank_mono (mlBlockedSpdpSubspace_le_inc _ _ _ _))

end GodMoveTopCoefficientMinor

#print axioms GodMoveTopCoefficientMinor.coeff_pderiv
#print axioms GodMoveTopCoefficientMinor.coeff_iterDerivList
#print axioms GodMoveTopCoefficientMinor.complementary_coefficient_identity
#print axioms GodMoveTopCoefficientMinor.derivativeRows_linearIndependent
#print axioms GodMoveTopCoefficientMinor.choose_le_strict_rank_of_top_coeff
#print axioms GodMoveTopCoefficientMinor.choose_le_inclusive_rank_of_top_coeff
