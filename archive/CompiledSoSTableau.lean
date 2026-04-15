/-
  CompiledSoSTableau.lean — Paper §17 Sum-of-Squares Compiled Polynomial
  built from CompiledTableau, with P-side rank bound via locality counting.

  ## Paper Reference

  §17.1: P̃_{M,n}(x,τ) = 1 - Σ_{C∈C} C(x,τ)²

  §17.3: P-side rank bound via locality counting (Theorem 92).

  The locality counting argument for the SoS form:
  - ∂_S(1 - Σ C²) = -Σ ∂_S(C²)  (linearity)
  - ∂_S(C²) = 0 unless S ⊆ vars(C²) ⊆ support(C), |support(C)| ≤ 10
  - Each surviving term has vars ⊆ support(C), giving ≤ 2^10 monomials
  - Total spanning set: ≤ numConstraints × 2^10 ≤ n^10 × 2^10 ≤ n^200
-/
import PallLean.CookLevinDefs
import PallLean.MultilinearSPDP
import PallLean.IterDerivHelpers
import PallLean.LocalityRankBound
import PallLean.MlProjFar
import PallLean.GodMoveReal
import Mathlib.Tactic

namespace CompiledSoSTableau

open SPDP MultilinearSPDP MvPolynomial TuringMachine PaperFaithfulSeparation

attribute [local instance] Classical.dec

/-! ## Step 1: Define compiledPolySoS from CompiledTableau -/

/-- The sum-of-squares violation polynomial: Σ_C C(x,τ)² -/
noncomputable def violationSoS {M : DTM} {n : ℕ} (T : CompiledTableau M n) :
    MvPolynomial (Fin T.numVars) ℚ :=
  (T.constraints.map (fun (c : LocalConstraint T.numVars) => c.poly ^ 2)).sum

/-- The compiled polynomial in sum-of-squares form:
    P̃_{M,n} = 1 - Σ_C C(x,τ)²
    Paper §17.1. -/
noncomputable def compiledPolySoS {M : DTM} {n : ℕ} (T : CompiledTableau M n) :
    MvPolynomial (Fin T.numVars) ℚ :=
  1 - violationSoS T

/-! ## Step 2: Degree bound -/

/-- C² has totalDegree ≤ 12 when C has totalDegree ≤ 6. -/
theorem sq_degree_le {N : ℕ} (c : LocalConstraint N) :
    (c.poly ^ 2).totalDegree ≤ 12 := by
  rw [sq]
  calc (c.poly * c.poly).totalDegree
      ≤ c.poly.totalDegree + c.poly.totalDegree := MvPolynomial.totalDegree_mul c.poly c.poly
    _ ≤ 6 + 6 := Nat.add_le_add c.degree_bound c.degree_bound
    _ = 12 := by omega

/-- The sum Σ C² has totalDegree ≤ 12. -/
theorem violationSoS_degree {M : DTM} {n : ℕ} (T : CompiledTableau M n) :
    (violationSoS T).totalDegree ≤ 12 := by
  unfold violationSoS
  induction T.constraints with
  | nil => simp [MvPolynomial.totalDegree_zero]
  | cons c rest ih =>
    simp only [List.map_cons, List.sum_cons]
    calc (c.poly ^ 2 + (rest.map (fun (c : LocalConstraint T.numVars) => c.poly ^ 2)).sum).totalDegree
        ≤ max (c.poly ^ 2).totalDegree
          (rest.map (fun (c : LocalConstraint T.numVars) => c.poly ^ 2)).sum.totalDegree :=
          MvPolynomial.totalDegree_add _ _
      _ ≤ max 12 12 := max_le_max (sq_degree_le c) ih
      _ = 12 := by omega

/-- compiledPolySoS has totalDegree ≤ 12. -/
theorem compiledPolySoS_degree {M : DTM} {n : ℕ} (T : CompiledTableau M n) :
    (compiledPolySoS T).totalDegree ≤ 12 := by
  unfold compiledPolySoS
  calc (1 - violationSoS T).totalDegree
      ≤ max (1 : MvPolynomial _ ℚ).totalDegree (violationSoS T).totalDegree :=
        MvPolynomial.totalDegree_sub _ _
    _ ≤ max 0 12 := by
        apply max_le_max
        · simp [MvPolynomial.totalDegree_one]
        · exact violationSoS_degree T
    _ = 12 := by omega

/-! ## Step 3: For κ ≥ 13, rank = 0 (degree vanishing) -/

/-- For κ ≥ 13 > 12 = degree(compiledPolySoS), all κ-th derivatives vanish. -/
theorem compiledPolySoS_rank_zero_large_kappa {M : DTM} {n : ℕ} (T : CompiledTableau M n)
    (κ : ℕ) (hκ : κ ≥ 13) (ℓ : ℕ) :
    mlBlockedSpdpRank T.partition κ ℓ (compiledPolySoS T) = 0 := by
  unfold mlBlockedSpdpRank
  have hdeg := compiledPolySoS_degree T
  have hsub : mlBlockedSpdpSubspace T.partition κ ℓ (compiledPolySoS T) = ⊥ := by
    rw [eq_bot_iff, mlBlockedSpdpSubspace]
    apply Submodule.span_le.mpr
    intro q ⟨S, m, hlen, _, _, _, hq⟩
    have hzero : iterDerivList S (compiledPolySoS T) = 0 :=
      iterDerivList_eq_zero_of_totalDegree_lt S _ (by omega)
    rw [hq, hzero, mul_zero, mlProj_zero]
    exact Submodule.zero_mem _
  rw [hsub]
  exact finrank_bot ℚ _

/-! ## Step 4: Linearity infrastructure for iterDerivList over List.sum -/

/-- iterDerivList distributes over List.sum. -/
theorem iterDerivList_list_sum {N : ℕ}
    (S : List (Fin N)) (ps : List (MvPolynomial (Fin N) ℚ)) :
    iterDerivList S ps.sum = (ps.map (fun p => iterDerivList S p)).sum := by
  induction ps with
  | nil =>
    simp only [List.sum_nil, List.map_nil]
    induction S with
    | nil => simp [iterDerivList]
    | cons i rest ih =>
      simp only [iterDerivList, List.foldl_cons]
      rw [map_zero (MvPolynomial.pderiv i)]
      exact ih
  | cons p rest ih =>
    simp only [List.sum_cons, List.map_cons, List.sum_cons]
    rw [IterDerivHelpers.iterDerivList_add, ih]

/-! ## Step 5: vars of C² are contained in support(C) -/

/-- vars(c.poly²) ⊆ c.support -/
theorem vars_sq_subset_support {N : ℕ} (c : LocalConstraint N) :
    (c.poly ^ 2).vars ⊆ c.support := by
  rw [sq]
  intro x hx
  have := MvPolynomial.vars_mul c.poly c.poly hx
  simp only [Finset.mem_union] at this
  exact this.elim (fun h => c.vars_contained h) (fun h => c.vars_contained h)

/-! ## Step 6: iterDerivList S (C²) = 0 when S has element outside support(C) -/

/-- If S contains a variable not in c.support, then iterDerivList S (c.poly²) = 0. -/
theorem iterDerivList_sq_zero_of_not_subset {N : ℕ}
    (c : LocalConstraint N) (S : List (Fin N))
    (hS : ∃ v, v ∈ S ∧ v ∉ c.support) :
    iterDerivList S (c.poly ^ 2) = 0 := by
  obtain ⟨v, hv_mem, hv_not⟩ := hS
  exact IterDerivHelpers.iterDerivList_eq_zero_of_mem_notMem_vars S v (c.poly ^ 2) hv_mem
    (fun hv => hv_not (vars_sq_subset_support c hv))

/-! ## Step 7: Helper lemmas for the spanning argument -/

/-- m * (list.map f cs).sum = (list.map (fun c => m * f c) cs).sum -/
theorem mul_list_map_sum {N : ℕ}
    (m : MvPolynomial (Fin N) ℚ)
    {α : Type*} (cs : List α) (f : α → MvPolynomial (Fin N) ℚ) :
    m * (cs.map f).sum = (cs.map (fun c => m * f c)).sum := by
  induction cs with
  | nil => simp
  | cons c rest ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, ih]

/-- mlProj distributes over List.sum. -/
theorem mlProj_list_sum {N : ℕ}
    (ps : List (MvPolynomial (Fin N) ℚ)) :
    mlProj ps.sum = (ps.map mlProj).sum := by
  induction ps with
  | nil => simp [mlProj_zero]
  | cons p rest ih =>
    simp only [List.sum_cons, List.map_cons, List.sum_cons]
    rw [mlProj_add, ih]

/-- If every element of a list lies in a submodule, so does the sum. -/
theorem list_sum_mem_submodule {N : ℕ}
    {W : Submodule ℚ (MvPolynomial (Fin N) ℚ)}
    (ps : List (MvPolynomial (Fin N) ℚ))
    (h : ∀ p, p ∈ ps → p ∈ W) :
    ps.sum ∈ W := by
  induction ps with
  | nil =>
    simp only [List.sum_nil]
    exact Submodule.zero_mem _
  | cons p rest ih =>
    simp only [List.sum_cons]
    apply Submodule.add_mem _
    · exact h p (List.mem_cons.mpr (Or.inl rfl))
    · exact ih (fun q hq => h q (List.mem_cons.mpr (Or.inr hq)))

/-! ## Step 8: The core spanning lemma for a single constraint -/

set_option maxHeartbeats 400000 in
/-- A single-constraint generator: mlProj(m * iterDerivList S (c.poly²)) lies in
    span(mlMonomialBasis(c.support)) when m.vars ⊆ S.toFinset.

    When S has element outside c.support, the generator is 0. -/
theorem single_constraint_generator_in_span {N : ℕ}
    (c : LocalConstraint N)
    (S : List (Fin N)) (m : MvPolynomial (Fin N) ℚ)
    (hvars_m : m.vars ⊆ S.toFinset) :
    mlProj (m * iterDerivList S (c.poly ^ 2)) ∈
      Submodule.span ℚ (↑(MlProjFar.mlMonomialBasis c.support) : Set _) := by
  by_cases hS_sub : ∀ v, v ∈ S → v ∈ c.support
  · -- All of S is in c.support; generator has vars ⊆ c.support
    have hm_vars : m.vars ⊆ c.support :=
      Finset.Subset.trans hvars_m (fun x hx => hS_sub x (List.mem_toFinset.mp hx))
    have hpoly_vars : (c.poly ^ 2).vars ⊆ c.support := vars_sq_subset_support c
    have hgen_vars : (mlProj (m * iterDerivList S (c.poly ^ 2))).vars ⊆ c.support :=
      Finset.Subset.trans
        (LocalityRankBound.mlProj_mul_iterDerivList_vars S m (c.poly ^ 2))
        (Finset.union_subset hm_vars hpoly_vars)
    have hgen_ml : ∀ α ∈ (mlProj (m * iterDerivList S (c.poly ^ 2))).support,
        Finsupp.IsMultilinear α := by
      intro α hα
      by_contra h_neg
      have : MvPolynomial.coeff α (mlProj (m * iterDerivList S (c.poly ^ 2))) = 0 := by
        show (Finsupp.filter (fun β => Finsupp.IsMultilinear β)
          (m * iterDerivList S (c.poly ^ 2))) α = 0
        rw [Finsupp.filter_apply]
        exact if_neg h_neg
      exact absurd this (Finsupp.mem_support_iff.mp hα)
    exact MlProjFar.mlProj_in_span_of_vars_subset
      (mlProj (m * iterDerivList S (c.poly ^ 2))) c.support hgen_ml hgen_vars
  · -- S has element outside c.support; term vanishes
    push_neg at hS_sub
    obtain ⟨v, hv_mem, hv_not⟩ := hS_sub
    rw [iterDerivList_sq_zero_of_not_subset c S ⟨v, hv_mem, hv_not⟩,
        mul_zero, mlProj_zero]
    exact Submodule.zero_mem _

/-! ## Step 9: The union basis and cardinality -/

/-- The union of mlMonomialBasis(c.support) over all constraints. -/
noncomputable def constraintBasisUnion {M : DTM} {n : ℕ} (T : CompiledTableau M n) :
    Finset (MvPolynomial (Fin T.numVars) ℚ) :=
  T.constraints.toFinset.biUnion (fun (c : LocalConstraint T.numVars) =>
    MlProjFar.mlMonomialBasis c.support)

/-- Card bound: |constraintBasisUnion| ≤ numConstraints × 2^10 -/
theorem constraintBasisUnion_card {M : DTM} {n : ℕ} (T : CompiledTableau M n) :
    (constraintBasisUnion T).card ≤ T.constraints.length * 2 ^ 10 := by
  unfold constraintBasisUnion
  calc (T.constraints.toFinset.biUnion _).card
      ≤ ∑ c ∈ T.constraints.toFinset, (MlProjFar.mlMonomialBasis c.support).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ T.constraints.toFinset, 2 ^ 10 := by
        apply Finset.sum_le_sum
        intro c _
        calc (MlProjFar.mlMonomialBasis c.support).card
            ≤ 2 ^ c.support.card := MlProjFar.mlMonomialBasis_card c.support
          _ ≤ 2 ^ 10 := Nat.pow_le_pow_right (by omega) c.support_bound
    _ = T.constraints.toFinset.card * 2 ^ 10 := by simp [Finset.sum_const]
    _ ≤ T.constraints.length * 2 ^ 10 :=
        Nat.mul_le_mul_right _ T.constraints.toFinset_card_le

/-- For the Cook-Levin compilation, |constraintBasisUnion| ≤ n^200. -/
theorem constraintBasisUnion_card_le_pow {M : DTM} {n : ℕ} (T : CompiledTableau M n)
    (hn : n ≥ 2) :
    (constraintBasisUnion T).card ≤ n ^ 200 := by
  calc (constraintBasisUnion T).card
      ≤ T.constraints.length * 2 ^ 10 := constraintBasisUnion_card T
    _ ≤ n ^ 10 * 2 ^ 10 := Nat.mul_le_mul_right _ T.constraints_poly
    _ = 2 ^ 10 * n ^ 10 := by ring
    _ ≤ n ^ 10 * n ^ 10 := by
        apply Nat.mul_le_mul_right
        calc (2 : ℕ) ^ 10 = 1024 := by norm_num
          _ ≤ 2 ^ 10 := le_refl _
          _ ≤ n ^ 10 := Nat.pow_le_pow_left hn 10
    _ = n ^ 20 := by rw [← pow_add]
    _ ≤ n ^ 200 := Nat.pow_le_pow_right (by omega : 1 ≤ n) (by omega)

/-! ## Step 10: The full SPDP subspace spanning lemma -/

/-- iterDerivList S (compiledPolySoS T) expressed via linearity.
    For |S| ≥ 1:
    iterDerivList S (1 - Σ C²) = -Σ_c iterDerivList S (c.poly²) -/
theorem iterDerivList_compiledPolySoS {M : DTM} {n : ℕ}
    (T : CompiledTableau M n)
    (S : List (Fin T.numVars)) (hS : S.length ≥ 1) :
    iterDerivList S (compiledPolySoS T) =
      -(T.constraints.map (fun (c : LocalConstraint T.numVars) =>
          iterDerivList S (c.poly ^ 2))).sum := by
  unfold compiledPolySoS
  rw [IterDerivHelpers.iterDerivList_sub]
  have h1 : iterDerivList S (1 : MvPolynomial (Fin T.numVars) ℚ) = 0 :=
    LocalityRankBound.iterDerivList_one_eq_zero S hS
  rw [h1, zero_sub]
  unfold violationSoS
  rw [iterDerivList_list_sum, List.map_map]
  rfl

/-- Each constraint's local basis is a subset of the full constraint basis union. -/
theorem mlMonomialBasis_subset_constraintBasisUnion {M : DTM} {n : ℕ}
    (T : CompiledTableau M n) (c : LocalConstraint T.numVars)
    (hc : c ∈ T.constraints) :
    ↑(MlProjFar.mlMonomialBasis c.support) ⊆ ↑(constraintBasisUnion T) := by
  intro b hb
  show b ∈ constraintBasisUnion T
  unfold constraintBasisUnion
  exact Finset.mem_biUnion.mpr ⟨c, List.mem_toFinset.mpr hc, hb⟩

/-- A generator from constraint c lies in span(constraintBasisUnion T). -/
theorem constraint_generator_in_full_span {M : DTM} {n : ℕ}
    (T : CompiledTableau M n) (c : LocalConstraint T.numVars)
    (hc : c ∈ T.constraints)
    (S : List (Fin T.numVars)) (m : MvPolynomial (Fin T.numVars) ℚ)
    (hvars : m.vars ⊆ S.toFinset) :
    mlProj (m * iterDerivList S (c.poly ^ 2)) ∈
      Submodule.span ℚ (↑(constraintBasisUnion T) : Set _) :=
  Submodule.span_mono
    (mlMonomialBasis_subset_constraintBasisUnion T c hc)
    (single_constraint_generator_in_span c S m hvars)

/-- A mapped list sum of generators lies in span(constraintBasisUnion T). -/
theorem mapped_sum_in_span {M : DTM} {n : ℕ}
    (T : CompiledTableau M n)
    (S : List (Fin T.numVars)) (m : MvPolynomial (Fin T.numVars) ℚ)
    (hvars : m.vars ⊆ S.toFinset)
    (cs : List (LocalConstraint T.numVars))
    (hcs : ∀ c, c ∈ cs → c ∈ T.constraints) :
    (cs.map (fun (c : LocalConstraint T.numVars) =>
      mlProj (m * iterDerivList S (c.poly ^ 2)))).sum ∈
      Submodule.span ℚ (↑(constraintBasisUnion T) : Set _) := by
  apply list_sum_mem_submodule
  intro p hp
  rw [List.mem_map] at hp
  obtain ⟨c, hc_mem, rfl⟩ := hp
  exact constraint_generator_in_full_span T c (hcs c hc_mem) S m hvars

set_option maxHeartbeats 1600000 in
/-- The SPDP subspace of compiledPolySoS is contained in span(constraintBasisUnion). -/
theorem spdp_subspace_le_span {M : DTM} {n : ℕ}
    (T : CompiledTableau M n) (κ ℓ : ℕ) (hκ : κ ≥ 1) :
    mlBlockedSpdpSubspace T.partition κ ℓ (compiledPolySoS T) ≤
      Submodule.span ℚ (↑(constraintBasisUnion T) : Set _) := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, hlen, _hdeg, hvars, _hadm, hq⟩
  rw [hq]
  rw [iterDerivList_compiledPolySoS T S (by omega)]
  rw [mul_neg, GodMoveReal.mlProj_neg]
  apply Submodule.neg_mem
  rw [mul_list_map_sum, mlProj_list_sum, List.map_map]
  exact mapped_sum_in_span T S m hvars T.constraints (fun c hc => hc)

/-! ## Step 11: The P-side rank bound -/

/-- P-side rank bound for compiledPolySoS via locality counting.

    Paper §17.3 (Theorem 92): Γ_{κ,ℓ}(P̃_{M,n}) ≤ n^O(1).

    For the SoS polynomial, this is trivial via the locality counting argument:
    each SPDP generator lies in span(mlMonomialBasis(c.support)) for some
    constraint c, and the union of these bases has cardinality ≤ n^200.
-/
theorem compiledPolySoS_rank_le {M : DTM} {n : ℕ} (T : CompiledTableau M n)
    (hn : n ≥ 2) (κ ℓ : ℕ) (hκ : κ ≥ 1) :
    mlBlockedSpdpRank T.partition κ ℓ (compiledPolySoS T) ≤ n ^ 200 := by
  show Module.finrank ℚ (mlBlockedSpdpSubspace T.partition κ ℓ (compiledPolySoS T)) ≤ n ^ 200
  exact le_trans
    (le_trans (Submodule.finrank_mono (spdp_subspace_le_span T κ ℓ hκ))
      (finrank_span_finset_le_card _))
    (constraintBasisUnion_card_le_pow T hn)

set_option maxHeartbeats 1600000 in
/-- Corollary: For the Cook-Levin compilation, compiledPolySoS has rank ≤ n^200.
    This is the paper's P-side bound (Theorem 92) for the SoS form. -/
theorem cook_levin_sos_rank_le (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    mlBlockedSpdpRank (cook_levin_compilation M n hn htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPolySoS (cook_levin_compilation M n hn htb hns)) ≤ n ^ 200 := by
  apply compiledPolySoS_rank_le _ hn
  exact Nat.log_pos (by omega) (by omega)

end CompiledSoSTableau
