/-
  LocalityRankBound.lean — P-side compiled rank bound

  Paper §9 / §17.3, Theorem 92:

  For the product polynomial P = ∏ᵢ (1 - Cᵢ) where each Cᵢ touches ≤ d₀ variables:

  The P-side rank bound uses profile compression (§9): rows of the SPDP matrix
  with the same constraint-type histogram ("profile") contribute to the same
  subspace. The number of distinct profiles is polynomial, giving:

    Γ_{κ,ℓ}(P) ≤ poly(n)

  The profile compression argument is not yet formalized. The P-side bound is
  stated as an axiom in PaperFaithfulSeparation.lean (`p_side_rank_bound_for_cook_levin`).

  This file provides:
  1. General-purpose lemmas about SPDP subspaces (locality, spanning sets, etc.)
     that are valid for any polynomial form.
  2. A re-export of the P-side axiom for use by SeparationFinal.lean.

  Historical note: this file previously contained a complete proof of the P-side
  bound for the sum-of-squares form 1 - Σ Cᵢ². That proof used linearity of
  differentiation and subadditivity of SPDP rank across summands. The product
  form ∏(1-Cᵢ) requires profile compression instead, because the Leibniz rule
  for products yields numConstraints^κ terms (superpolynomial by simple counting).
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

/-! ## Local Spanning Set Construction

The key idea: every generator mlProj(m · ∂_S p) of the SPDP subspace
can be expressed as a linear combination of "local basis vectors" —
multilinear monomials on a bounded number of variables.

These general-purpose lemmas apply to ANY polynomial form (product or SoS). -/

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

    This is the combinatorial core of the per-summand rank bound. -/
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

The theorem states: given a spanning set G with |G| ≤ N^200,
the multilinear blocked SPDP rank is bounded by N^200.

This is a general-purpose tool used by the P-side argument. -/

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

/-! ## General-Purpose Lemmas for SPDP Subspace Analysis -/

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

/-! ## P-side Bound for Cook-Levin Compilation

The compiled polynomial is now P = ∏(1-Cᵢ) (product form, matching the paper §17.1).

For the product form, simple locality counting gives a superpolynomial bound:
  numConstraints^κ = poly(n)^{log n} = n^{c log n}

The paper's profile compression (§9, Theorem 92) reduces this to polynomial
by grouping SPDP rows with identical constraint-type histograms ("profiles").
The number of distinct profiles is bounded by a polynomial in n.

Profile compression is not yet formalized. The P-side bound is therefore
obtained from the axiom `p_side_rank_bound_for_cook_levin` declared in
PaperFaithfulSeparation.lean. -/

/-- The P-side rank bound for cook_levin_compilation.

    For the product polynomial P = ∏(1-Cᵢ), this requires profile compression
    (paper §9, Theorem 92). The bound is obtained from the axiom
    `p_side_rank_bound_for_cook_levin` in PaperFaithfulSeparation.lean. -/
theorem p_side_bound_for_cook_levin (M : DTM) (n : ℕ) (hn : n ≥ 2) :
    mlBlockedSpdpRank (PaperFaithfulSeparation.cook_levin_compilation M n hn).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (PaperFaithfulSeparation.compiledPoly
        (PaperFaithfulSeparation.cook_levin_compilation M n hn)) ≤ n ^ 200 :=
  PaperFaithfulSeparation.p_side_rank_bound_for_cook_levin M n hn

end LocalityRankBound
