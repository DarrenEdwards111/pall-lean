import GodMoveMonomialMinor

/-!
# Exact shifted-derivative space of the full squarefree product

With distinct-variable blocks, derivative order `k ≤ n`, and shift allowance
at least `k`, the full monomial's strict SPDP space consists precisely of the
span of squarefree monomials missing at most `k` variables. The construction
extends a missing-variable set to a `k`-set and shifts back the added variables.
This is an exact algebraic characterization, not a runtime upper bound.
-/

namespace GodMoveFullShiftProductSpace

open MvPolynomial SPDP MultilinearSPDP
open GodMoveMonomialMinor
open scoped BigOperators

/-- Squarefree monomials whose complements have size at most `k`. -/
noncomputable def highDegreeSpace (n k : ℕ) : Submodule ℚ (Poly n) :=
  Submodule.span ℚ {p | ∃ R : Finset (Fin n), R.card ≤ k ∧ p = derivativeRow R}

instance highDegreeSpace_finite (n k : ℕ) : Module.Finite ℚ (highDegreeSpace n k) := by
  apply Module.Finite.span_of_finite
  apply (Set.finite_range (derivativeRow (n := n))).subset
  rintro p ⟨R, _, rfl⟩
  exact ⟨R, rfl⟩

theorem derivativeRow_mem_highDegreeSpace {n : ℕ} (k : ℕ) (R : Finset (Fin n))
    (hR : R.card ≤ k) : derivativeRow R ∈ highDegreeSpace n k :=
  Submodule.subset_span ⟨R, hR, rfl⟩

theorem monomial_mem_highDegreeSpace {n : ℕ} (k : ℕ) (a : Fin n →₀ ℕ)
    (ha : ∀ i, a i ≤ 1) (hcard : (Finset.univ \ a.support).card ≤ k) :
    monomial a (1 : ℚ) ∈ highDegreeSpace n k := by
  have heq : complementaryColumn (Finset.univ \ a.support) = a := by
    ext i
    by_cases hi : i ∈ a.support
    · have hn : a i ≠ 0 := Finsupp.mem_support_iff.mp hi
      have hone : a i = 1 := by have := ha i; omega
      simp [complementaryColumn, SymmetricPower.tagMonomial_apply, hi, hone]
    · have hz : a i = 0 := Finsupp.notMem_support_iff.mp hi
      simp [complementaryColumn, SymmetricPower.tagMonomial_apply, hi, hz]
  have h := derivativeRow_mem_highDegreeSpace k (Finset.univ \ a.support) hcard
  rwa [derivativeRow_eq_monomial, heq] at h

theorem polynomial_mem_highDegreeSpace {n : ℕ} (k : ℕ) (p : Poly n)
    (hp : IsMultilinear p)
    (hcard : ∀ a ∈ p.support, (Finset.univ \ a.support).card ≤ k) :
    p ∈ highDegreeSpace n k := by
  rw [p.as_sum]
  apply Submodule.sum_mem
  intro a ha
  rw [show monomial a (coeff a p) = coeff a p • monomial a (1 : ℚ) by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (monomial_mem_highDegreeSpace k a (hp a ha) (hcard a ha))

/-- Projection of any multiple of the complement of `S` misses at most the
variables of `S`; no constraint on the multiplier is needed. -/
theorem mlProj_mul_complement_mem {n : ℕ} (k : ℕ) (S : Finset (Fin n))
    (hS : S.card ≤ k) (q : Poly n) :
    mlProj (q * derivativeRow S) ∈ highDegreeSpace n k := by
  classical
  apply polynomial_mem_highDegreeSpace k
  · intro a ha
    change a ∈ (Finsupp.filter _ (q * derivativeRow S)).support at ha
    rw [Finsupp.support_filter] at ha
    exact (Finset.mem_filter.mp ha).2
  · intro a ha
    have hmul := mlProj_support_subset (q * derivativeRow S) ha
    obtain ⟨b, hb, c, hc, hsum⟩ := Finset.mem_add.mp (support_mul _ _ hmul)
    have hc' : c = complementaryColumn S := by
      rw [derivativeRow_eq_monomial] at hc
      exact Finset.mem_singleton.mp (support_monomial_subset hc)
    have hsub : Finset.univ \ a.support ⊆ S := by
      intro i hi
      have hai : a i = 0 := Finsupp.notMem_support_iff.mp (Finset.mem_sdiff.mp hi).2
      by_contra hiS
      have hc1 : c i = 1 := by
        simp [hc', complementaryColumn, SymmetricPower.tagMonomial_apply, hiS]
      have hsum' := congrArg (fun d => d i) hsum
      simp only [Finsupp.add_apply, hc1, hai] at hsum'
      omega
    exact (Finset.card_le_card hsub).trans hS

/-- Multiplying back the variables added to a derivative set restores the
desired complementary monomial exactly. -/
theorem shift_derivativeRow {n : ℕ} (R S : Finset (Fin n)) (hRS : R ⊆ S) :
    (∏ i ∈ S \ R, (X i : Poly n)) * derivativeRow S = derivativeRow R := by
  rw [MlProjFar.prod_X_eq_monomial_tag, derivativeRow_eq_monomial,
    derivativeRow_eq_monomial, monomial_mul, mul_one]
  apply congrArg (fun d : Fin n →₀ ℕ => monomial d (1 : ℚ))
  ext i
  by_cases hiR : i ∈ R
  · have hiS := hRS hiR
    simp [complementaryColumn, SymmetricPower.tagMonomial_apply, hiR, hiS]
  · by_cases hiS : i ∈ S <;>
      simp [complementaryColumn, SymmetricPower.tagMonomial_apply, hiR, hiS]

theorem highDegreeSpace_le_strict_spdp (n k ell : ℕ) (hk : k ≤ n) (hell : k ≤ ell) :
    highDegreeSpace n k ≤ mlBlockedSpdpSubspace (discreteBlocks n) k ell (fullMonomial n) := by
  apply Submodule.span_le.mpr
  rintro p ⟨R, hR, rfl⟩
  obtain ⟨S, hRS, _, hSc⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ R) hR (by simpa using hk)
  apply Submodule.subset_span
  refine ⟨S.toList, (∏ i ∈ S \ R, (X i : Poly n)), ?_, ?_, ?_,
    discrete_admissible S, ?_⟩
  · simpa using hSc
  · calc
      _ ≤ ∑ i ∈ S \ R, (X i : Poly n).totalDegree := totalDegree_finset_prod _ _
      _ = (S \ R).card := by simp
      _ ≤ S.card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ ell := hSc ▸ hell
  · intro i hi
    have hmem := vars_prod (fun j => (X j : Poly n)) hi
    obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hmem
    simp only [vars_X, Finset.mem_singleton] at hij
    subst i
    simpa using (Finset.mem_sdiff.mp hj).1
  · change derivativeRow R = mlProj ((∏ i ∈ S \ R, (X i : Poly n)) * derivativeRow S)
    rw [shift_derivativeRow R S hRS, derivativeRow_mlProj]

theorem strict_spdp_le_highDegreeSpace (n k ell : ℕ) :
    mlBlockedSpdpSubspace (discreteBlocks n) k ell (fullMonomial n) ≤ highDegreeSpace n k := by
  apply Submodule.span_le.mpr
  rintro p ⟨S, q, hlen, _, _, hadm, rfl⟩
  have hcard : S.toFinset.card = k := by rw [List.toFinset_card_of_nodup hadm.1, hlen]
  have hrow : iterDerivList S (fullMonomial n) = derivativeRow S.toFinset := by
    rw [derivativeRow_eq_complement_product]
    exact iterDerivList_prod_X Finset.univ S hadm.1 (fun _ _ => Finset.mem_univ _)
  rw [hrow]
  exact mlProj_mul_complement_mem k S.toFinset hcard.le q

/-- Exact source row space for sufficient shifts and a legal derivative order. -/
theorem strict_spdp_eq_highDegreeSpace (n k ell : ℕ) (hk : k ≤ n) (hell : k ≤ ell) :
    mlBlockedSpdpSubspace (discreteBlocks n) k ell (fullMonomial n) = highDegreeSpace n k :=
  le_antisymm (strict_spdp_le_highDegreeSpace n k ell)
    (highDegreeSpace_le_strict_spdp n k ell hk hell)

/-- Above the number of variables, the strict space has no admissible rows. -/
theorem strict_spdp_eq_bot_of_lt (n k ell : ℕ) (hk : n < k) :
    mlBlockedSpdpSubspace (discreteBlocks n) k ell (fullMonomial n) = ⊥ := by
  apply le_antisymm ?_ bot_le
  apply Submodule.span_le.mpr
  rintro p ⟨S, q, hlen, _, _, hadm, _⟩
  have hcard : S.toFinset.card = k := by rw [List.toFinset_card_of_nodup hadm.1, hlen]
  have hle : S.toFinset.card ≤ n := by
    simpa using Finset.card_le_univ S.toFinset
  omega

end GodMoveFullShiftProductSpace

#print axioms GodMoveFullShiftProductSpace.monomial_mem_highDegreeSpace
#print axioms GodMoveFullShiftProductSpace.polynomial_mem_highDegreeSpace
#print axioms GodMoveFullShiftProductSpace.mlProj_mul_complement_mem
#print axioms GodMoveFullShiftProductSpace.shift_derivativeRow
#print axioms GodMoveFullShiftProductSpace.highDegreeSpace_le_strict_spdp
#print axioms GodMoveFullShiftProductSpace.strict_spdp_le_highDegreeSpace
#print axioms GodMoveFullShiftProductSpace.strict_spdp_eq_highDegreeSpace
#print axioms GodMoveFullShiftProductSpace.strict_spdp_eq_bot_of_lt
