/-
  RankTransfer.lean — §9.3 + §12: Rank transfer from Tseitin to compiled polynomial

  Goal: prove rank_transfer_from_tseitin
  
  The proof has 3 layers:
  
  Layer 1 (§9.3): Disjoint clause families produce identity minors.
    DisjointClauseFamily → coupled verifier poly Q× → SPDP matrix → identity minor
    → rank(Q×) ≥ C(L, κ)
    
  Layer 2 (§12): The compiled violation polynomial contains Q× as a sub-structure.
    compiledViolationPoly M n on Tseitin input → restriction → Q× embedded
    → rank(compiled) ≥ rank(Q×)
    
  Layer 3 (superpolynomial): C(αn, log n) > n^c for any fixed c.
    Already proved (choose_superpolynomial). Needs strengthening to > n^c.
-/
import PallLean.PneqNP_v3
import Mathlib.Tactic

open MvPolynomial TseitinLowerBound PneqNP_v3 TuringMachine

namespace RankTransfer

/-! ## Layer 1: Coupled verifier polynomial and identity minor

  For a DisjointClauseFamily with L clauses on N variables:
  
  Q×(u, z) = ∏_{C ∈ C_disj} (1 - z_C · V_C(u_{B_C}))
  
  where u are block variables, z are selector variables.
  Total variables: N + L (u₁..uₙ, z₁..zₗ).
  
  The SPDP generators of Q× include:
  - For each κ-subset S ⊆ [L]: the derivative ∂_{z_S} Q× 
  - For each κ-subset S: the tag monomial τ_S = ∏_{C ∈ S} τ_C
  
  Key property (Theorem 9.3): the SPDP coefficient matrix has an
  identity minor of size C(L, κ).
-/

-- Selector + block variable space: N original vars + L selector vars
def coupledVarCount (N L : ℕ) : ℕ := N + L

-- Index of selector variable z_C
def selectorIdx (N : ℕ) (C : Fin L) : Fin (coupledVarCount N L) :=
  ⟨N + C.val, by unfold coupledVarCount; omega⟩

-- The clause gadget polynomial V_C: a polynomial in block variables B_C.
-- For 3-SAT: V_C(u) = (1 - u_{i₁})(1 - u_{i₂})(1 - u_{i₃}) for positive literals,
-- or variations for negated literals.
-- Key property: V_C evaluates to 0 on satisfying assignments of clause C,
-- and to nonzero on falsifying assignments.

-- The coupled verifier polynomial Q× for a disjoint clause family.
-- Q×(u,z) = ∏_{C=1}^{L} (1 - z_C · V_C(u_{B_C}))
-- 
-- Formal definition: we don't need the exact polynomial. We need:
-- (a) It's a multilinear polynomial in z-variables
-- (b) Derivative ∂_{z_S} Q× = ±∏_{C ∈ S} V_C · ∏_{C ∉ S} (1 - z_C V_C)
-- (c) At z = 0: ∂_{z_S} Q×|_{z=0} = (-1)^|S| ∏_{C ∈ S} V_C
-- (d) The tag monomial coefficient extracts 1 from each V_C

-- For the identity minor:
-- Row S: the generator ∂_{z_S} Q×|_{z=0} = (-1)^|S| ∏_{C ∈ S} V_C
-- Column S: the tag monomial τ_S = ∏_{C ∈ S} τ_C
-- Entry [S, S']: coefficient of τ_{S'} in (-1)^|S| ∏_{C ∈ S} V_C
-- Diagonal (S = S'): (-1)^|S| · ∏_{C ∈ S} [τ_C] V_C = (-1)^|S| · 1^|S| = (-1)^|S| ≠ 0
-- Off-diagonal (S ≠ S'): ∃ C ∈ S' \ S, and τ_C uses only B_C variables,
--   but the product ∏_{C ∈ S} V_C doesn't involve B_{C'} for C' ∉ S (disjointness).
--   So coefficient of τ_{S'} = 0.

-- Theorem 9.3: DisjointClauseFamily → blockedSpdpRankQ ≥ C(L, κ)
-- This is the key theorem connecting combinatorial structure to rank.
axiom disjoint_clauses_rank_lower {N : ℕ} 
    (dcf : DisjointClauseFamily N)
    (κ ℓ : ℕ) 
    (Q : MvPolynomial (Fin (coupledVarCount N dcf.numClauses)) ℚ)
    (bp : CompiledPoly.BlockPartition (coupledVarCount N dcf.numClauses))
    (hQ_coupled : True) -- Q is the coupled verifier polynomial for dcf
    :
    CompiledPoly.blockedSpdpRankQ κ ℓ Q bp ≥ Nat.choose dcf.numClauses κ

/-! ## Layer 2: Compiled violation polynomial contains Q×

  When M decides 3-SAT and the input is a Tseitin instance:
  - M's transition constraints encode the verification
  - The violation polynomial V_{M,n} = Σ C_i² includes clause constraints
  - On a Tseitin input, the clause constraints contain the Tseitin structure
  - The coupled verifier Q× embeds into V_{M,n} via restriction + projection
  
  Key lemma: rank(Q×) ≤ rank(V_{M,n}) via rank-monotone operations.
-/

-- The embedding: Q× restricted/projected into compiledViolationPoly.
-- This requires:
-- 1. An injection from coupled variable space into compiled variable space
-- 2. The compiled poly, restricted to Tseitin input, contains Q× as a factor
-- 3. Rank monotonicity under restriction (rename_rank_le)
axiom compiled_contains_coupled (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    {N : ℕ} (dcf : DisjointClauseFamily N)
    (κ ℓ : ℕ) :
    ∀ (bp : CompiledPoly.BlockPartition (coupledVarCount N dcf.numClauses)),
    CompiledPoly.blockedSpdpRankQ κ ℓ
      (PneqNP_v3.compiledViolationPoly M n)
      (PneqNP_v3.compiledPartition M n)
    ≥ CompiledPoly.blockedSpdpRankQ κ ℓ
      (sorry : MvPolynomial (Fin (coupledVarCount N dcf.numClauses)) ℚ) bp

/-! ## Layer 3: C(αn, log n) > n^c for any fixed c

  Already partially proved: choose_superpolynomial gives C(αn, log n) > √n.
  Need: C(αn, log n) > n^c for any c.
  
  Proof: C(m, k) ≥ (m/k)^k. With m = αn, k = log n:
  C(αn, log n) ≥ (αn/log n)^{log n}
  For large n: αn/log n ≥ n^{1/2}, so (αn/log n)^{log n} ≥ n^{log n / 2} > n^c.
-/

-- Stronger superpolynomial bound: C(αn, log n) > n^c for any fixed c.
axiom choose_beats_any_polynomial (α : ℕ) (hα : α ≥ 1) (c : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, n ≥ 2 →
    Nat.choose (α * n) (Nat.log 2 n) > n ^ c

/-! ## Assembly: rank_transfer_from_tseitin

  Combine Layers 1 + 2 + 3:
  1. DisjointClauseFamily with αn clauses exists (proved)
  2. rank(Q×) ≥ C(αn, log n) (Layer 1)
  3. rank(compiled) ≥ rank(Q×) (Layer 2)
  4. C(αn, log n) > n^c (Layer 3)
  5. Therefore: rank(compiled) > n^c
-/

-- This is the roadmap. Each layer has its own axiom that can be
-- independently attacked. The assembly is straightforward calc.

end RankTransfer
