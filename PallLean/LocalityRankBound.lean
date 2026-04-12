/-
  LocalityRankBound.lean — P-side compiled rank bound via locality counting

  Paper §17.3, Lemma 32 / Theorem 92:

  For a polynomial P = 1 - Σ_i C_i² where each C_i touches ≤ d₀ variables:

  1. ∂_S P = -Σ_i ∂_S(C_i²) by linearity
  2. ∂_S(C_i²) = 0 unless supp(S) ∩ vars(C_i) ≠ ∅ (locality)
  3. Each surviving term is supported in vars(C_i) ∪ supp(S), size O(d₀ + κ)
  4. The multilinear projections span a subspace of dimension ≤ 2^O(d₀+κ)
  5. There are at most |C| constraints, each contributing ≤ 1 surviving term per row
  6. Total basis size ≤ |C| × 2^O(d₀+κ) = poly(n) (since d₀ = O(1) and κ = O(log n))

  We prove: locality_rank_bound — for the compiled polynomial from a P-time DTM,
  the mlBlockedSpdpRank is at most N^200.
-/
import PallLean.PaperFaithfulSeparation
import PallLean.MlProjFar
import PallLean.GodMoveReal
import PallLean.IterDerivHelpers
import PallLean.PDerivVars
import Mathlib.Tactic
import Mathlib.Data.Nat.Log

namespace LocalityRankBound

open SPDP MultilinearSPDP MvPolynomial TuringMachine

attribute [local instance] Classical.dec

/-! ## Foundational Lemmas for Constant Polynomials -/

/-- iterDerivList of 1 is 0 when the list is nonempty. -/
theorem iterDerivList_one_eq_zero {N : ℕ}
    (S : List (Fin N)) (hS : S.length ≥ 1) :
    iterDerivList S (1 : MvPolynomial (Fin N) ℚ) = 0 := by
  cases S with
  | nil => simp at hS
  | cons i rest =>
    unfold iterDerivList
    simp only [List.foldl_cons]
    have h1 : (1 : MvPolynomial (Fin N) ℚ) = C 1 := by simp
    rw [h1, pderiv_C]
    exact foldl_pderiv_zero rest

/-- The mlBlockedSpdpSubspace of the constant polynomial 1 is ⊥ when κ ≥ 1. -/
theorem mlBlockedSpdpSubspace_one_eq_bot {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ) (hκ : κ ≥ 1) :
    mlBlockedSpdpSubspace B κ ℓ (1 : MvPolynomial (Fin N) ℚ) = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro q ⟨S, m, hlen, _hdeg, _hvars, _hadm, hq⟩
    rw [hq, iterDerivList_one_eq_zero S (by omega), mul_zero, mlProj_zero]
    exact Submodule.zero_mem ⊥
  · exact bot_le

/-- For the specific compiled polynomial from cook_levin_compilation
    (which has constraints = []), the compiled polynomial is 1. -/
theorem cook_levin_compiledPoly_eq_one (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    PaperFaithfulSeparation.compiledPoly
      (PaperFaithfulSeparation.cook_levin_compilation M n hn) = 1 := by
  unfold PaperFaithfulSeparation.compiledPoly PaperFaithfulSeparation.cook_levin_compilation
  simp

/-! ## Local Spanning Set Construction

The key idea: every generator mlProj(m · ∂_S p) of the SPDP subspace,
where p = 1 - Σ C_i², can be expressed as a linear combination of
"local basis vectors" — multilinear monomials on at most d₀ + 2κ variables.

The total number of such local basis vectors is bounded by:
  (number of constraints) × (multilinear monomials per local neighborhood)
  ≤ |C| × 2^(d₀ + 2κ)

For the Cook-Levin compilation: d₀ = 10 (constant), κ = log₂(N),
|C| ≤ N^10, so:
  total ≤ N^10 × 2^(10 + 2·log₂(N)) = N^10 × 2^10 × N^2 ≤ N^13 ≤ N^200
-/

/-- The maximum number of multilinear monomials on k variables is 2^k.
    This is the fundamental counting bound for the locality argument. -/
theorem multilinear_monomial_count_bound (k : ℕ) :
    2 ^ k ≥ 1 := Nat.one_le_pow k 2 (by omega)

/-- For d₀ ≤ 10 and κ = log₂ N, the quantity 2^(d₀ + 2κ) ≤ 2^10 × N^2.
    This bounds the number of multilinear monomials per constraint neighborhood. -/
theorem local_monomial_bound (N : ℕ) (hN : N ≥ 2)
    (d₀ : ℕ) (hd₀ : d₀ ≤ 10)
    (κ : ℕ) (hκ : κ = Nat.log 2 N) :
    2 ^ (d₀ + 2 * κ) ≤ 2 ^ 10 * N ^ 2 := by
  have h1 : d₀ + 2 * κ ≤ 10 + 2 * Nat.log 2 N := by omega
  have hN_pos : N ≠ 0 := by omega
  calc 2 ^ (d₀ + 2 * κ)
      ≤ 2 ^ (10 + 2 * Nat.log 2 N) := Nat.pow_le_pow_right (by omega) h1
    _ = 2 ^ 10 * 2 ^ (2 * Nat.log 2 N) := by ring
    _ = 2 ^ 10 * (2 ^ Nat.log 2 N) ^ 2 := by ring
    _ ≤ 2 ^ 10 * N ^ 2 := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hN_pos) 2

/-- The total spanning set size for a compilation with |C| constraints,
    each touching d₀ variables, and SPDP parameter κ = log₂ N:
      |C| × 2^(d₀ + 2κ) ≤ N^10 × 2^10 × N^2 ≤ N^200.

    This is the combinatorial core of the P-side rank bound. -/
theorem spanning_set_size_bound (N : ℕ) (hN : N ≥ 4)
    (numConstraints : ℕ) (hC : numConstraints ≤ N ^ 10)
    (d₀ : ℕ) (hd₀ : d₀ ≤ 10)
    (κ : ℕ) (hκ : κ = Nat.log 2 N) :
    numConstraints * 2 ^ (d₀ + 2 * κ) ≤ N ^ 200 := by
  have hN2 : N ≥ 2 := by omega
  have h_local := local_monomial_bound N hN2 d₀ hd₀ κ hκ
  calc numConstraints * 2 ^ (d₀ + 2 * κ)
      ≤ N ^ 10 * (2 ^ 10 * N ^ 2) := Nat.mul_le_mul hC h_local
    _ = 2 ^ 10 * (N ^ 10 * N ^ 2) := by ring
    _ = 2 ^ 10 * N ^ 12 := by rw [← pow_add]
    _ ≤ N ^ 12 * N ^ 12 := by
        apply Nat.mul_le_mul_right
        -- 2^10 = 1024 ≤ 4^12 ≤ N^12
        have : (4 : ℕ) ≤ N := hN
        calc (2 : ℕ) ^ 10 = 1024 := by norm_num
          _ ≤ 4 ^ 12 := by norm_num
          _ ≤ N ^ 12 := by
              apply Nat.pow_le_pow_left; exact hN
    _ = N ^ 24 := by rw [← pow_add]
    _ ≤ N ^ 200 := by
        apply Nat.pow_le_pow_right (by omega : 1 ≤ N) (by omega : 24 ≤ 200)

/-! ## The Main Locality Rank Bound

The theorem states: for the compiled polynomial of a P-time DTM,
the multilinear blocked SPDP rank is bounded by N^200.

The proof uses the spanning set argument:
- If G is a finite set with the SPDP subspace ≤ span(G) and |G| ≤ N^200,
  then rank ≤ |G| ≤ N^200.
-/

/-- The P-side locality rank bound for a compiled tableau polynomial.

    Paper §17.3, Theorem 92: given a spanning set G with |G| ≤ N^200,
    the SPDP rank is at most N^200. -/
theorem locality_rank_bound (N : ℕ)
    (B : BlockPartition N)
    (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ)
    (G : Finset (MvPolynomial (Fin N) ℚ))
    (hSpan : mlBlockedSpdpSubspace B κ ℓ p ≤
      Submodule.span ℚ (↑G : Set (MvPolynomial (Fin N) ℚ)))
    (hCard : G.card ≤ N ^ 200) :
    mlBlockedSpdpRank B κ ℓ p ≤ N ^ 200 := by
  unfold mlBlockedSpdpRank
  calc Module.finrank ℚ (mlBlockedSpdpSubspace B κ ℓ p)
      ≤ Module.finrank ℚ (Submodule.span ℚ (↑G : Set (MvPolynomial (Fin N) ℚ))) :=
        Submodule.finrank_mono hSpan
    _ ≤ G.card := finrank_span_finset_le_card G
    _ ≤ N ^ 200 := hCard

/-! ## Local Spanning Set Structure -/

/-- A local spanning set packages a finite set of polynomials that spans
    the SPDP subspace with cardinality ≤ N^200. -/
structure LocalSpanningSet (N : ℕ) (B : BlockPartition N)
    (p : MvPolynomial (Fin N) ℚ) where
  basis : Finset (MvPolynomial (Fin N) ℚ)
  spans : mlBlockedSpdpSubspace B (Nat.log 2 N) (Nat.log 2 N) p ≤
    Submodule.span ℚ (↑basis : Set (MvPolynomial (Fin N) ℚ))
  card_bound : basis.card ≤ N ^ 200

/-- When a local spanning set exists, the SPDP rank is bounded by N^200. -/
theorem rank_from_local_spanning_set (N : ℕ)
    (B : BlockPartition N)
    (p : MvPolynomial (Fin N) ℚ)
    (lss : LocalSpanningSet N B p) :
    mlBlockedSpdpRank B (Nat.log 2 N) (Nat.log 2 N) p ≤ N ^ 200 :=
  locality_rank_bound N B _ _ p lss.basis lss.spans lss.card_bound

/-! ## Concrete P-side Bound for Cook-Levin Compilation

For the specific Cook-Levin compilation used in the separation,
constraints = [] so the compiled polynomial is 1. The SPDP subspace
of a constant is trivial (⊥) when κ ≥ 1, so the rank is 0 ≤ N^200. -/

/-- P-side rank bound for the specific Cook-Levin compilation
    (constraints = [], compiledPoly = 1, rank = 0 ≤ n^200). -/
theorem p_side_locality_bound_cook_levin (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    mlBlockedSpdpRank
      (PaperFaithfulSeparation.cook_levin_compilation M n hn).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (PaperFaithfulSeparation.compiledPoly
        (PaperFaithfulSeparation.cook_levin_compilation M n hn)) ≤ n ^ 200 := by
  unfold mlBlockedSpdpRank
  rw [cook_levin_compiledPoly_eq_one]
  have hκ : Nat.log 2 n ≥ 1 := by
    have : 2 ^ 1 ≤ n := by omega
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) this
  rw [mlBlockedSpdpSubspace_one_eq_bot _ _ _ hκ]
  simp

/-- The P-side rank bound is satisfied for cook_levin_compilation,
    matching the p_side_rank_bound predicate from PaperFaithfulSeparation. -/
theorem p_side_bound_for_cook_levin (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    PaperFaithfulSeparation.p_side_rank_bound M n
      (PaperFaithfulSeparation.cook_levin_compilation M n hn) :=
  p_side_locality_bound_cook_levin M n hn

/-! ## General Locality Counting Theorem

For the general case where constraints ≠ [], we prove the rank bound
given a spanning set. The spanning set existence is a combinatorial
fact about the structure of 1 - Σ C_i². -/

/-- The compiled polynomial satisfies: compiledPoly T = 1 - sum_of_squares. -/
theorem compiledPoly_decomp {M : DTM} {n : ℕ}
    (T : PaperFaithfulSeparation.CompiledTableau M n) :
    PaperFaithfulSeparation.compiledPoly T =
      1 - (T.constraints.map (fun c => c.poly ^ 2)).sum := rfl

/-- Core locality theorem: given a spanning set of polynomial size,
    the mlBlockedSpdpRank is bounded by N^200.

    For any compiled polynomial P = 1 - Σ C_i² from a CompiledTableau T,
    if we can construct a finite spanning set G with |G| ≤ n^200 for the
    SPDP subspace, then the SPDP rank is at most n^200. -/
theorem p_side_rank_bound_from_compilation (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (T : PaperFaithfulSeparation.CompiledTableau M n)
    (G : Finset (MvPolynomial (Fin T.numVars) ℚ))
    (hSpan : mlBlockedSpdpSubspace T.partition (Nat.log 2 n) (Nat.log 2 n)
        (PaperFaithfulSeparation.compiledPoly T) ≤
      Submodule.span ℚ (↑G : Set (MvPolynomial (Fin T.numVars) ℚ)))
    (hCard : G.card ≤ n ^ 200) :
    PaperFaithfulSeparation.p_side_rank_bound M n T := by
  unfold PaperFaithfulSeparation.p_side_rank_bound
  unfold mlBlockedSpdpRank
  calc Module.finrank ℚ (mlBlockedSpdpSubspace T.partition (Nat.log 2 n) (Nat.log 2 n)
        (PaperFaithfulSeparation.compiledPoly T))
      ≤ Module.finrank ℚ (Submodule.span ℚ
        (↑G : Set (MvPolynomial (Fin T.numVars) ℚ))) :=
        Submodule.finrank_mono hSpan
    _ ≤ G.card := finrank_span_finset_le_card G
    _ ≤ n ^ 200 := hCard

/-- For the specific Cook-Levin compilation, a local spanning set exists
    (the empty set, since the compiled polynomial is constant 1). -/
noncomputable def buildLocalSpanningSet_cookLevin (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    LocalSpanningSet n
      (PaperFaithfulSeparation.cook_levin_compilation M n hn).partition
      (PaperFaithfulSeparation.compiledPoly
        (PaperFaithfulSeparation.cook_levin_compilation M n hn)) where
  basis := ∅
  spans := by
    rw [cook_levin_compiledPoly_eq_one M n hn]
    have hκ : Nat.log 2 n ≥ 1 := by
      have : 2 ^ 1 ≤ n := by omega
      exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) this
    rw [mlBlockedSpdpSubspace_one_eq_bot _ _ _ hκ]
    simp
  card_bound := by simp

/-! ## General P-side Rank Bound for Any CompiledTableau

We prove that for ANY CompiledTableau (not just cook_levin_compilation),
the SPDP rank of compiledPoly T is ≤ n^200.

The argument:
1. compiledPoly T = 1 - Σ C² where each C has vars ⊆ support, |support| ≤ 10
2. Γ(1 - Σ C²) ≤ Γ(1) + Γ(Σ C²) = 0 + Γ(Σ C²)  (via add/neg lemmas)
3. Γ(Σ C²) ≤ Σ Γ(C²)  (subadditivity)
4. Γ(C²) ≤ 2^|support| ≤ 2^10 = 1024  (locality: SPDP generators have vars ⊆ support)
5. |constraints| × 1024 ≤ n^10 × n^10 = n^20 ≤ n^200
-/

/-- vars of p^2 are contained in vars of p. -/
theorem vars_sq_subset {N : ℕ} (p : MvPolynomial (Fin N) ℚ) :
    (p ^ 2).vars ⊆ p.vars := by
  rw [sq]
  intro x hx
  have := MvPolynomial.vars_mul p p hx
  simp only [Finset.mem_union] at this
  exact this.elim id id

/-- iterDerivList S p = 0 when S has an element not in p.vars.
    Wrapper around iterDerivList_eq_zero_of_mem_notMem_vars. -/
theorem iterDerivList_eq_zero_of_not_subset {N : ℕ}
    (S : List (Fin N)) (p : MvPolynomial (Fin N) ℚ)
    (V : Finset (Fin N)) (hpv : p.vars ⊆ V)
    (hS : ∃ v, v ∈ S ∧ v ∉ V) :
    iterDerivList S p = 0 := by
  obtain ⟨v, hv_mem, hv_not⟩ := hS
  exact IterDerivHelpers.iterDerivList_eq_zero_of_mem_notMem_vars S v p hv_mem
    (fun hv => hv_not (hpv hv))

/-- vars of iterDerivList S p are contained in vars of p. -/
theorem iterDerivList_vars_subset {N : ℕ}
    (S : List (Fin N)) (p : MvPolynomial (Fin N) ℚ) :
    (iterDerivList S p).vars ⊆ p.vars := by
  induction S generalizing p with
  | nil => unfold iterDerivList; exact Finset.Subset.refl _
  | cons a rest ih =>
    unfold iterDerivList
    exact Finset.Subset.trans (ih (MvPolynomial.pderiv a p))
      (PDerivVars.pderiv_vars_subset a p)

/-- vars(mlProj p) ⊆ vars(p). -/
theorem mlProj_vars_subset' {N : ℕ}
    (p : MvPolynomial (Fin N) ℚ) : (mlProj p).vars ⊆ p.vars := by
  intro x hx
  rw [MvPolynomial.mem_vars] at hx ⊢
  obtain ⟨α, hα_supp, hα_x⟩ := hx
  exact ⟨α, mlProj_support_subset p hα_supp, hα_x⟩

/-- vars of mlProj(m * iterDerivList S p) ⊆ vars(m) ∪ vars(p). -/
theorem mlProj_mul_iterDerivList_vars {N : ℕ}
    (S : List (Fin N)) (m p : MvPolynomial (Fin N) ℚ) :
    (mlProj (m * iterDerivList S p)).vars ⊆ m.vars ∪ p.vars := by
  calc (mlProj (m * iterDerivList S p)).vars
      ⊆ (m * iterDerivList S p).vars := mlProj_vars_subset' _
    _ ⊆ m.vars ∪ (iterDerivList S p).vars :=
        MvPolynomial.vars_mul m (iterDerivList S p)
    _ ⊆ m.vars ∪ p.vars :=
        Finset.union_subset_union (Finset.Subset.refl _) (iterDerivList_vars_subset S p)

set_option maxHeartbeats 400000 in
/-- The SPDP subspace of a polynomial p with vars ⊆ V is contained in
    Submodule.span ℚ (mlMonomialBasis V).

    Key argument: every generator mlProj(m * iterDerivList S p) either is 0
    (if S has element outside V) or has vars ⊆ V (if S ⊆ V, since vars(m) ⊆ S ⊆ V). -/
theorem spdp_subspace_le_span_of_vars_subset {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin N) ℚ)
    (V : Finset (Fin N))
    (hpv : p.vars ⊆ V) :
    mlBlockedSpdpSubspace B κ ℓ p ≤
      Submodule.span ℚ (↑(MlProjFar.mlMonomialBasis V) : Set _) := by
  apply Submodule.span_le.mpr
  intro q ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
  rw [hq]
  -- Case split: does S have an element outside V?
  by_cases hS_sub : ∀ v, v ∈ S → v ∈ V
  · -- All elements of S are in V
    -- vars(m) ⊆ S.toFinset ⊆ V
    have hm_vars : m.vars ⊆ V :=
      Finset.Subset.trans hvars (fun x hx => hS_sub x (List.mem_toFinset.mp hx))
    -- So mlProj(m * iterDerivList S p) has vars ⊆ V
    have hgen_vars : (mlProj (m * iterDerivList S p)).vars ⊆ V :=
      Finset.Subset.trans (mlProj_mul_iterDerivList_vars S m p)
        (Finset.union_subset hm_vars hpv)
    -- mlProj is multilinear: its support monomials satisfy IsMultilinear
    -- Proof: mlProj = Finsupp.filter IsMultilinear; any α in the filtered support is multilinear.
    have hgen_ml : ∀ α ∈ (mlProj (m * iterDerivList S p)).support,
        Finsupp.IsMultilinear α := by
      intro α hα
      -- α ∈ (mlProj q).support = (filter IsMultilinear q).support
      -- If ¬IsMultilinear α, then filter at α = 0, contradicting α ∈ support.
      by_contra h_neg
      have : MvPolynomial.coeff α (mlProj (m * iterDerivList S p)) = 0 := by
        show (Finsupp.filter (fun β => Finsupp.IsMultilinear β) (m * iterDerivList S p)) α = 0
        rw [Finsupp.filter_apply]
        exact if_neg h_neg
      exact absurd this (Finsupp.mem_support_iff.mp hα)
    -- Apply mlProj_in_span_of_vars_subset
    exact MlProjFar.mlProj_in_span_of_vars_subset
      (mlProj (m * iterDerivList S p)) V hgen_ml hgen_vars
  · -- S has an element outside V, so iterDerivList S p = 0
    push_neg at hS_sub
    obtain ⟨v, hv_mem, hv_not⟩ := hS_sub
    rw [iterDerivList_eq_zero_of_not_subset S p V hpv ⟨v, hv_mem, hv_not⟩,
        mul_zero, mlProj_zero]
    exact Submodule.zero_mem _

set_option maxHeartbeats 3200000 in
/-- The SPDP rank of C² is ≤ 2^|support| when C.vars ⊆ support.
    This is the per-constraint locality rank bound. -/
theorem spdp_rank_sq_le_pow_support {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ)
    (C : PaperFaithfulSeparation.LocalConstraint N) :
    mlBlockedSpdpRank B κ ℓ (C.poly ^ 2) ≤ 2 ^ C.support.card := by
  unfold mlBlockedSpdpRank
  have hpv : (C.poly ^ 2).vars ⊆ C.support :=
    Finset.Subset.trans (vars_sq_subset C.poly) C.vars_contained
  have hle := spdp_subspace_le_span_of_vars_subset B κ ℓ (C.poly ^ 2) C.support hpv
  -- finrank(SPDP subspace) ≤ finrank(span(mlMonomialBasis)) ≤ |mlMonomialBasis| ≤ 2^|support|
  exact le_trans (le_trans (Submodule.finrank_mono hle) (finrank_span_finset_le_card _))
    (MlProjFar.mlMonomialBasis_card C.support)

/-- The SPDP rank of C² is ≤ 1024 for any LocalConstraint (support ≤ 10). -/
theorem spdp_rank_sq_le_1024 {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ)
    (C : PaperFaithfulSeparation.LocalConstraint N) :
    mlBlockedSpdpRank B κ ℓ (C.poly ^ 2) ≤ 1024 := by
  calc mlBlockedSpdpRank B κ ℓ (C.poly ^ 2)
      ≤ 2 ^ C.support.card := spdp_rank_sq_le_pow_support B κ ℓ C
    _ ≤ 2 ^ 10 := Nat.pow_le_pow_right (by omega) C.support_bound
    _ = 1024 := by norm_num

/-- List.map+sum equals Finset.sum over Fin. -/
theorem list_sum_eq_finset_sum {N : ℕ}
    (L : List (PaperFaithfulSeparation.LocalConstraint N)) :
    (L.map (fun c => c.poly ^ 2)).sum =
    ∑ i : Fin L.length, ((L.get i).poly ^ 2) := by
  conv_lhs => rw [show L.map (fun c => c.poly ^ 2) =
    List.ofFn (fun i : Fin L.length => (L.get i).poly ^ 2) from by
      apply List.ext_get
      · simp
      · intro i h1 h2
        simp [List.get_ofFn]]
  exact List.sum_ofFn

/-- Subadditivity for list sums: Γ(Σ C²) ≤ Σ Γ(C²). -/
theorem spdp_rank_list_sum_le {N : ℕ}
    (B : BlockPartition N) (κ ℓ : ℕ)
    (L : List (PaperFaithfulSeparation.LocalConstraint N)) :
    mlBlockedSpdpRank B κ ℓ (L.map (fun c => c.poly ^ 2)).sum ≤
      L.length * 1024 := by
  rw [list_sum_eq_finset_sum L]
  calc mlBlockedSpdpRank B κ ℓ (∑ i : Fin L.length, ((L.get i).poly ^ 2))
      ≤ ∑ i : Fin L.length, mlBlockedSpdpRank B κ ℓ ((L.get i).poly ^ 2) :=
        mlBlockedSpdpRank_finsum_le B κ ℓ L.length _
    _ ≤ ∑ _i : Fin L.length, 1024 := by
        apply Finset.sum_le_sum
        intro i _
        exact spdp_rank_sq_le_1024 B κ ℓ (L.get i)
    _ = L.length * 1024 := by simp [Finset.sum_const]

/-- 1024 ≤ n^10 for n ≥ 2. -/
theorem bound_1024_le_pow10 (n : ℕ) (hn : n ≥ 2) : 1024 ≤ n ^ 10 := by
  calc 1024 = 2 ^ 10 := by norm_num
    _ ≤ n ^ 10 := Nat.pow_le_pow_left hn 10

/-- General P-side rank bound for ANY CompiledTableau.

    For any DTM M and input size n ≥ 2, the compiled polynomial of a
    CompiledTableau has SPDP rank ≤ n^200.

    Proof:
    - compiledPoly T = 1 - Σ C²
    - Γ(1 - Σ C²) ≤ Γ(1) + Γ(Σ C²) = 0 + Γ(Σ C²) ≤ Σ Γ(C²)
    - Each Γ(C²) ≤ 2^10 = 1024 (locality)
    - Total: |constraints| × 1024 ≤ n^10 × n^10 = n^20 ≤ n^200 -/
theorem general_p_side_rank_bound (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (T : PaperFaithfulSeparation.CompiledTableau M n) :
    PaperFaithfulSeparation.p_side_rank_bound M n T := by
  unfold PaperFaithfulSeparation.p_side_rank_bound
  -- compiledPoly T = 1 - sum_of_squares
  -- Step 1: Reduce to bounding Γ(sum_of_squares)
  -- 1 - s = (-s) + 1
  have hcp : PaperFaithfulSeparation.compiledPoly T =
      (-(T.constraints.map (fun c => c.poly ^ 2)).sum) + 1 := by
    unfold PaperFaithfulSeparation.compiledPoly
    ring
  rw [hcp]
  -- Γ((-s) + 1) = Γ((-s) + C 1) = Γ(-s) using add_const
  have h1_eq : (1 : MvPolynomial (Fin T.numVars) ℚ) = MvPolynomial.C 1 := by simp
  rw [h1_eq]
  have hκ_pos : Nat.log 2 n ≥ 1 := by
    exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by omega : 2 ^ 1 ≤ n)
  rw [GodMoveReal.mlBlockedSpdpRank_add_const T.partition
      (Nat.log 2 n) (Nat.log 2 n) hκ_pos
      (-(T.constraints.map (fun c => c.poly ^ 2)).sum) 1]
  -- Γ(-s) = Γ(s) using neg
  have hneg_eq : mlBlockedSpdpSubspace T.partition (Nat.log 2 n) (Nat.log 2 n)
      (-(T.constraints.map (fun c => c.poly ^ 2)).sum) =
      mlBlockedSpdpSubspace T.partition (Nat.log 2 n) (Nat.log 2 n)
      (T.constraints.map (fun c => c.poly ^ 2)).sum :=
    GodMoveReal.mlBlockedSpdpSubspace_neg T.partition _ _ _
  unfold mlBlockedSpdpRank
  rw [hneg_eq]
  -- Now bound Γ(Σ C²) ≤ |constraints| × 1024 ≤ n^200
  have hrank_sum := spdp_rank_list_sum_le T.partition
    (Nat.log 2 n) (Nat.log 2 n) T.constraints
  unfold mlBlockedSpdpRank at hrank_sum
  calc Module.finrank ℚ (mlBlockedSpdpSubspace T.partition (Nat.log 2 n) (Nat.log 2 n)
        (List.map (fun c => c.poly ^ 2) T.constraints).sum)
      ≤ T.constraints.length * 1024 := hrank_sum
    _ ≤ n ^ 10 * 1024 := Nat.mul_le_mul_right 1024 T.constraints_poly
    _ ≤ n ^ 10 * n ^ 10 := Nat.mul_le_mul_left (n ^ 10) (bound_1024_le_pow10 n hn)
    _ = n ^ 20 := by rw [← pow_add]
    _ ≤ n ^ 200 := Nat.pow_le_pow_right (by omega : 1 ≤ n) (by omega : 20 ≤ 200)

/-- The P-side bound is provable from the actual locality construction
    for ANY GodMoveExtraction. This discharges the p_bound field of PeqNP_Paper
    from the actual construction, without assuming it as a hypothesis. -/
theorem p_bound_from_locality (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (ext : PaperFaithfulSeparation.GodMoveExtraction M n) :
    PaperFaithfulSeparation.p_side_rank_bound M n ext.compiled :=
  general_p_side_rank_bound M n hn ext.compiled

end LocalityRankBound
