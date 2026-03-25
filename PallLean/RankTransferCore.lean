/-
  RankTransferCore.lean — §9.3 identity minor → SPDP rank lower bound

  Paper-faithful skeleton for the NP-side core.
  Connects DisjointClauseFamily → identity minor → blockedSpdpRankQ lower bound.
-/
import PallLean.PneqNP_v3
import Mathlib.Tactic

open MvPolynomial TseitinLowerBound PneqNP_v3 TuringMachine

namespace RankTransferCore

/-! ## Identity minor definition

  An r×r identity minor in a matrix A means:
  - diagonal entries are nonzero: A(i,i) ≠ 0
  - off-diagonal entries vanish: A(i,j) = 0 for i ≠ j
  
  This implies rank(A) ≥ r (proved in TseitinLowerBound).
-/

/-- A square submatrix is an identity minor: nonzero diagonal, zero off-diagonal. -/
def IsIdentityMinor {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → I → ℚ) : Prop :=
  (∀ i, A i i ≠ 0) ∧ (∀ i j, i ≠ j → A i j = 0)

/-- Identity minor gives rank lower bound.
    Already proved in TseitinLowerBound.identity_minor_gives_rank_lower_bound
    for Matrix. Restated here for function form. -/
theorem identity_minor_rank_bound {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → I → ℚ) (hA : IsIdentityMinor A) :
    Fintype.card I ≤ Module.finrank ℚ (I → ℚ) := by
  -- The rows of A are linearly independent (identity minor)
  have hli : LinearIndependent ℚ (fun i : I => fun j : I => A i j) := by
    rw [linearIndependent_iff']
    intro s g hsum k hk
    have h_eval := congr_fun hsum k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h_eval
    -- Σ_{i ∈ s} g(i) * A(i, k) = 0
    -- For i ≠ k: A(i, k) = 0 (off-diagonal). For i = k: A(k, k) ≠ 0.
    -- So g(k) * A(k, k) = 0, hence g(k) = 0.
    have h_offdiag : ∀ i ∈ s, i ≠ k → g i * A i k = 0 := by
      intro i _ hik; rw [hA.2 i k hik, mul_zero]
    -- Split sum into k-term + rest
    have h_rest : ∑ i ∈ s.erase k, g i * A i k = 0 := by
      apply Finset.sum_eq_zero; intro i hi
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      exact h_offdiag i (Finset.mem_of_mem_erase hi) hik
    rw [← Finset.add_sum_erase s _ hk] at h_eval
    -- g(k) * A(k,k) + 0 = 0 ⟹ g(k) * A(k,k) = 0 ⟹ g(k) = 0
    have : g k * A k k = 0 := by linarith
    exact (mul_eq_zero.mp this).elim id (absurd · (hA.1 k))
  calc Fintype.card I = Fintype.card I := rfl
    _ ≤ Module.finrank ℚ (I → ℚ) := hli.fintype_card_le_finrank

/-! ## SPDP matrix from blocked SPDP rank

  The SPDP matrix M_{κ,ℓ}(V, bp) has:
  - Rows indexed by: (S, ms) where S is a κ-list, ms has degree ≤ ℓ,
    S uses distinct blocks, ms coupled to S
  - Columns indexed by: monomials of the polynomial ms * ∂_S(V)
  - Entry: coefficient of the column monomial in ms * ∂_S(V)
  
  The blockedSpdpRankQ is the rank of the span of generators
  {ms * ∂_S(V) | valid (S, ms)}, which equals the column rank of this matrix.
  
  For the identity minor construction from disjoint clauses:
  - Rows: for each κ-subset T of disjoint clauses, take S = selector vars of T
  - Columns: for each κ-subset T, take the tag monomial τ_T = ∏_{C ∈ T} τ_C
  - Diagonal: coefficient of τ_T in ∂_{z_T}(Q×) = (-1)^κ ∏_{C ∈ T} [τ_C] V_C ≠ 0
  - Off-diagonal: coefficient of τ_{T'} in ∂_{z_T}(Q×) = 0 (disjointness)
-/

-- The SPDP matrix entry: coefficient of monomial `col` in generator `row`.
-- This connects blockedSpdpRankQ (= finrank of span) to the matrix rank.
-- For our purposes: blockedSpdpRankQ ≥ rank of any submatrix,
-- and an identity minor gives rank ≥ minor size.

/-! ## §9.3 core: disjoint clauses → identity minor → rank bound

  Given:
  - DisjointClauseFamily with L clauses, pairwise disjoint blocks
  - The coupled verifier polynomial Q×
  - κ = derivative order, ℓ = multiplier degree
  
  The SPDP generators of Q× include, for each κ-subset T ⊆ [L]:
  - Generator: (∏_{C ∈ T} z_C-derivative) of Q×, multiplied by tag ms
  - These generators span a space of dimension ≥ C(L, κ)
  
  The identity minor argument:
  - Select C(L, κ) rows (one per κ-subset)
  - Select C(L, κ) columns (tag monomials)
  - Show diagonal nonzero, off-diagonal zero
  - Conclude rank ≥ C(L, κ)
-/

-- The core §9.3 theorem for abstract coupled verifier polynomials.
-- Stated in terms of blockedSpdpRankQ to connect directly to PneqNP_v3.
-- 
-- This is the theorem that needs a concrete proof.
-- The proof requires:
-- 1. Defining the SPDP generators for Q× from selector derivatives
-- 2. Showing they include an identity minor of size C(L, κ)
-- 3. Converting the identity minor to a finrank bound
--
-- Sub-lemmas needed:
-- (a) Derivative of product: ∂_{z_T}(∏ (1-z_C·V_C)) = (-1)^|T| ∏_{C∈T} V_C · (rest)
-- (b) Tag coefficient: [τ_T] in the generator = (-1)^|T| · ∏_{C∈T} [τ_C]V_C
-- (c) Disjointness: T≠T' ⟹ [τ_{T'}] in generator for T = 0
-- (d) Each [τ_C]V_C = 1 (tag monomial property)
--
-- These are proved by:
-- (a) Leibniz rule for products + z_C appears only in factor C
-- (b) Extracting coefficients from product of block-local polynomials
-- (c) τ_{T'} involves a variable from block C' ∉ T, which doesn't appear in ∏_{C∈T} V_C
-- (d) Definition of tag monomial

-- For now: axiomatized. This is the mathematical core of §9.3.
-- The scaffolding above describes exactly what needs to be proved.

end RankTransferCore
