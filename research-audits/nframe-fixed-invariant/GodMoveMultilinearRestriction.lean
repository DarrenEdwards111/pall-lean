import PallLean.PiStarConcrete

/-!
# Constant restrictions preserve strict SPDP rank of multilinear sources

The restriction may fix variables to arbitrary rational constants. The source
multilinearity premise is essential: it prevents a discarded square in a fixed
variable from becoming a retained constant. The proof constructs the row-space
transport using the existing restriction itself, at unchanged parameters.
-/

namespace GodMoveMultilinearRestriction

open MvPolynomial SPDP MultilinearSPDP PiStarConcrete
open scoped BigOperators

variable {N : ℕ}

abbrev Poly := MvPolynomial (Fin N) ℚ

/-- Exponents remaining after the other variables are fixed. -/
def keptExponent (keep : Fin N → Prop) [DecidablePred keep]
    (a : Fin N →₀ ℕ) : Fin N →₀ ℕ := a.filter keep

/-- The scalar supplied by all fixed variables of a monomial. -/
def droppedScalar (keep : Fin N → Prop) [DecidablePred keep]
    (val : Fin N → ℚ) (a : Fin N →₀ ℕ) : ℚ :=
  (a.filter fun i => ¬ keep i).prod fun i e => val i ^ e

theorem piSubst_monomial (keep : Fin N → Prop) [DecidablePred keep]
    (val : Fin N → ℚ) (a : Fin N →₀ ℕ) (c : ℚ) :
    piSubst keep val (monomial a c) =
      monomial (keptExponent keep a) (c * droppedScalar keep val a) := by
  change substAlgHom keep val (monomial a c) = _
  unfold substAlgHom
  rw [aeval_monomial]
  change C c * a.prod (fun i e => substFn keep val i ^ e) = _
  rw [← Finsupp.prod_filter_mul_prod_filter_not keep a]
  have hk : (a.filter keep).prod (fun i e => substFn keep val i ^ e) =
      monomial (keptExponent keep a) (1 : ℚ) := by
    rw [← prod_X_pow_eq_monomial]
    apply Finset.prod_congr rfl
    intro i hi
    have hki := (Finset.mem_filter.mp hi).2
    simp [substFn, hki, keptExponent]
  have hd : (a.filter fun i => ¬ keep i).prod
      (fun i e => substFn keep val i ^ e) = C (droppedScalar keep val a) := by
    unfold droppedScalar Finsupp.prod
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    have hki := (Finset.mem_filter.mp hi).2
    simp [substFn, hki]
  rw [hk, hd]
  simp [mul_comm, C_mul_monomial]

theorem keptExponent_multilinear_iff
    (keep : Fin N → Prop) [DecidablePred keep] (a : Fin N →₀ ℕ)
    (ha : ∀ i, ¬ keep i → a i ≤ 1) :
    Finsupp.IsMultilinear (keptExponent keep a) ↔ Finsupp.IsMultilinear a := by
  constructor
  · intro h i
    by_cases hi : keep i
    · simpa [keptExponent, Finsupp.filter_apply, hi] using h i
    · exact ha i hi
  · intro h i
    by_cases hi : keep i <;> simp [keptExponent, hi, h i]

/-- Multilinear projection commutes with restriction when the dropped
variables already have degree at most one. Kept variables need no bound. -/
theorem mlProj_piSubst_comm_monomial
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    (a : Fin N →₀ ℕ) (c : ℚ) (ha : ∀ i, ¬ keep i → a i ≤ 1) :
    mlProj (piSubst keep val (monomial a c)) =
      piSubst keep val (mlProj (monomial a c)) := by
  rw [piSubst_monomial, mlProj_monomial, mlProj_monomial]
  have heq := keptExponent_multilinear_iff keep a ha
  by_cases h : Finsupp.IsMultilinear a
  · simp [h, heq.mpr h, piSubst_monomial]
  · have hk : ¬ Finsupp.IsMultilinear (keptExponent keep a) := fun hk => h (heq.mp hk)
    simp [h, hk]

theorem mlProj_piSubst_comm
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    (q : Poly (N := N))
    (hq : ∀ a ∈ q.support, ∀ i, ¬ keep i → a i ≤ 1) :
    mlProj (piSubst keep val q) = piSubst keep val (mlProj q) := by
  conv_lhs => rw [← support_sum_monomial_coeff q]
  conv_rhs => rw [← support_sum_monomial_coeff q]
  simp only [map_sum, show ∀ s : Finset (Fin N →₀ ℕ),
      ∀ f : (Fin N →₀ ℕ) → Poly (N := N), mlProj (∑ a ∈ s, f a) =
        ∑ a ∈ s, mlProj (f a) from fun s f => map_sum (mlProjHom ℚ) f s]
  apply Finset.sum_congr rfl
  intro a ha
  exact mlProj_piSubst_comm_monomial keep val a (coeff a q) (hq a ha)

/-- Constant restriction also preserves multilinearity of the polynomial. -/
theorem isMultilinear_piSubst
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    (p : Poly (N := N)) (hp : IsMultilinear p) :
    IsMultilinear (piSubst keep val p) := by
  intro b hb i
  rw [← support_sum_monomial_coeff p, map_sum] at hb
  obtain ⟨a, ha, hba⟩ := Finsupp.mem_support_finset_sum b hb
  rw [piSubst_monomial] at hba
  have heq := support_monomial_subset hba
  rw [Finset.mem_singleton] at heq
  rw [heq]
  by_cases hi : keep i <;> simp [keptExponent, hi, hp a ha i]

theorem piSubst_eq_self_of_vars_kept
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    (m : Poly (N := N)) (hm : ∀ i ∈ m.vars, keep i) :
    piSubst keep val m = m := by
  change aeval (substFn keep val) m = m
  calc
    _ = aeval X m :=
      eval₂Hom_congr' rfl (fun i hi _ => by simp [substFn, hm i hi]) rfl
    _ = m := by rw [aeval_X_left]; rfl

/-- Kept-supported shifts do not change the degree of a dropped variable. -/
theorem shifted_multilinear_dropped_bound
    (keep : Fin N → Prop) (m q : Poly (N := N))
    (hm : ∀ i ∈ m.vars, keep i) (hq : IsMultilinear q) :
    ∀ a ∈ (m * q).support, ∀ i, ¬ keep i → a i ≤ 1 := by
  intro a ha i hi
  obtain ⟨b, hb, d, hd, rfl⟩ := Finset.mem_add.mp (support_mul m q ha)
  have hb0 := support_kept_of_vars_kept keep hm b hb i hi
  simpa [Finsupp.add_apply, hb0] using hq d hd i

/-- An actual SPDP generator is transported by the same restriction map. -/
theorem restricted_generator_eq
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    (p : Poly (N := N)) (hp : IsMultilinear p)
    (S : List (Fin N)) (m : Poly (N := N))
    (hm : m.vars ⊆ S.toFinset) (hS : ∀ i ∈ S, keep i) :
    mlProj (m * iterDerivList S (piSubst keep val p)) =
      piSubst keep val (mlProj (m * iterDerivList S p)) := by
  have hmkept : ∀ i ∈ m.vars, keep i :=
    fun i hi => hS i (List.mem_toFinset.mp (hm hi))
  rw [iterDerivList_piSubst_allKept keep val S hS p]
  have hmul : m * piSubst keep val (iterDerivList S p) =
      piSubst keep val (m * iterDerivList S p) := by
    change m * substAlgHom keep val (iterDerivList S p) =
      substAlgHom keep val (m * iterDerivList S p)
    rw [map_mul]
    exact congrArg (fun z => z * substAlgHom keep val (iterDerivList S p))
      (piSubst_eq_self_of_vars_kept keep val m hmkept).symm
  rw [hmul]
  exact mlProj_piSubst_comm keep val _
    (shifted_multilinear_dropped_bound keep m _ hmkept
      (isMultilinear_iterDerivList S p hp))

/-- The restricted row space is contained in the image of the original
row space under the concrete constant-substitution map. -/
theorem mlBlockedSpdpSubspace_piSubst_le_map
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    (B : BlockPartition N) (k ell : ℕ) (p : Poly (N := N))
    (hp : IsMultilinear p) :
    mlBlockedSpdpSubspace B k ell (piSubst keep val p) ≤
      Submodule.map (piSubst keep val) (mlBlockedSpdpSubspace B k ell p) := by
  apply Submodule.span_le.mpr
  rintro q ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  by_cases hS : ∀ i ∈ S, keep i
  · rw [restricted_generator_eq keep val p hp S m hvars hS]
    exact ⟨mlProj (m * iterDerivList S p),
      Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩, rfl⟩
  · push_neg at hS
    rw [iterDerivList_piSubst_notKept keep val S hS p, mul_zero, mlProj_zero]
    exact Submodule.zero_mem _

/-- Arbitrary constant restriction is rank-nonincreasing on multilinear
sources, for the same block partition and derivative/shift parameters. -/
theorem mlBlockedSpdpRank_piSubst_le
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    (B : BlockPartition N) (k ell : ℕ) (p : Poly (N := N))
    (hp : IsMultilinear p) :
    mlBlockedSpdpRank B k ell (piSubst keep val p) ≤
      mlBlockedSpdpRank B k ell p := by
  unfold mlBlockedSpdpRank
  exact (Submodule.finrank_mono
    (mlBlockedSpdpSubspace_piSubst_le_map keep val B k ell p hp)).trans
    (Submodule.finrank_map_le _ _)

/-- The same concrete row transport holds for the inclusive derivative window. -/
theorem mlBlockedSpdpSubspaceInc_piSubst_le_map
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    (B : BlockPartition N) (k ell : ℕ) (p : Poly (N := N))
    (hp : IsMultilinear p) :
    mlBlockedSpdpSubspaceInc B k ell (piSubst keep val p) ≤
      Submodule.map (piSubst keep val) (mlBlockedSpdpSubspaceInc B k ell p) := by
  apply Submodule.span_le.mpr
  rintro q ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩
  by_cases hS : ∀ i ∈ S, keep i
  · rw [restricted_generator_eq keep val p hp S m hvars hS]
    exact ⟨mlProj (m * iterDerivList S p),
      Submodule.subset_span ⟨S, m, hlen, hdeg, hvars, hadm, rfl⟩, rfl⟩
  · push_neg at hS
    rw [iterDerivList_piSubst_notKept keep val S hS p, mul_zero, mlProj_zero]
    exact Submodule.zero_mem _

/-- Inclusive SPDP rank is also nonincreasing at unchanged parameters. -/
theorem mlBlockedSpdpRankInc_piSubst_le
    (keep : Fin N → Prop) [DecidablePred keep] (val : Fin N → ℚ)
    (B : BlockPartition N) (k ell : ℕ) (p : Poly (N := N))
    (hp : IsMultilinear p) :
    mlBlockedSpdpRankInc B k ell (piSubst keep val p) ≤
      mlBlockedSpdpRankInc B k ell p := by
  unfold mlBlockedSpdpRankInc
  exact (Submodule.finrank_mono
    (mlBlockedSpdpSubspaceInc_piSubst_le_map keep val B k ell p hp)).trans
    (Submodule.finrank_map_le _ _)

end GodMoveMultilinearRestriction

#print axioms GodMoveMultilinearRestriction.piSubst_monomial
#print axioms GodMoveMultilinearRestriction.mlProj_piSubst_comm
#print axioms GodMoveMultilinearRestriction.isMultilinear_piSubst
#print axioms GodMoveMultilinearRestriction.restricted_generator_eq
#print axioms GodMoveMultilinearRestriction.mlBlockedSpdpSubspace_piSubst_le_map
#print axioms GodMoveMultilinearRestriction.mlBlockedSpdpRank_piSubst_le
#print axioms GodMoveMultilinearRestriction.mlBlockedSpdpSubspaceInc_piSubst_le_map
#print axioms GodMoveMultilinearRestriction.mlBlockedSpdpRankInc_piSubst_le
