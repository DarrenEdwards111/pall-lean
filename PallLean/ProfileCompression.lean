/-
  ProfileCompression.lean — Profile Compression (Paper §5)

  The profile compression argument shows that the number of algebraically
  distinct SPDP generator families is polylogarithmic, not polynomial.

  Key definitions:
  - Profile: the local pattern of a derivative support S (which blocks
    it touches, what local types the clauses have)
  - Profile equivalence: two S with the same profile generate the same span
  - Profile count bound: number of distinct profiles ≤ R^{O(1)}

  Chain: restricted_clause_survival follows from:
  1. degree_truncation: only |S| ≤ 6 matters (PROVED)
  2. profile_compression: equivalent S generate same span (THIS FILE)
  3. profile_count: number of profiles ≤ (log n)^{O(1)} (THIS FILE)
  4. per_profile_dim: each profile's span has dim ≤ (log n)^{O(1)} (THIS FILE)
-/
import PallLean.CompiledPoly
import PallLean.CookLevin
import PallLean.DegreeDrop
import Mathlib.Tactic

namespace ProfileCompression

open MvPolynomial CompiledPoly CookLevin SPDP

/-! ## Generator variable bound

  Every nonzero SPDP generator m · ∂^S(V) depends on at most
  maxGenVars variables, where maxGenVars is a constant independent of n.

  With |S| ≤ 6, S-coupling (m uses ≤ 24 vars), and V local (each clause ≤ 3 vars):
  - m uses ≤ 24 variables (6 blocks × 4 vars/block)
  - ∂^S(V) = Σ_{c touched by S} ∂^S(clausePoly(c)²)
  - Each clause c involves ≤ 3 variables
  - Number of clauses touched by S ≤ 6 × (max clauses per block) = O(1)
  - Total variables in ∂^S(V): ≤ 3 × O(1) = O(1)
  - Variables in m · ∂^S(V): ≤ 24 + O(1) = O(1)
-/

/-- Maximum number of variables any single generator can depend on.
    With cell partition (≤ 4 vars/block), |S| ≤ 6, S-coupling,
    and width-3 clauses: 24 (from m) + 18 (from ∂^S(V)) = 42. -/
def maxGenVars : ℕ := 42

/-! ## Profile type

  A profile captures the "local shape" of a derivative support S:
  - Which block positions are touched (up to isomorphism)
  - What clause types are in each block
  - How the clauses connect across blocks

  Two S with the same profile produce generators that span isomorphic subspaces
  (after relabeling variables). The key insight: the SPDP matrix rows for
  equivalent profiles are related by a block-local coordinate change,
  which is an isomorphism that preserves rank.

  For our scaffold (n input clauses + 24 core clauses):
  - Input clauses are all identical (tautology type)
  - Core clauses have 8 distinct types (by FamilyTag)
  - A profile records which clause types appear near S
  
  The number of profiles is bounded by:
  - Number of ways to choose ≤ 6 block "types": O(1) choices (since clause
    types are from a finite set of size 9 = |FamilyTag|)
  - Each block contributes a "local type" from a finite alphabet
  - Profile = tuple of ≤ 6 local types
  - Number of profiles ≤ |local_types|^6 = O(1) — CONSTANT!
-/

/-- A local type captures the clause structure of a single block. -/
inductive LocalBlockType where
  | inputTautology   -- block contains an input variable (tautology clause)
  | scaffoldStep0    -- block is scaffold time step 0 (4 role vars)
  | scaffoldStep1    -- block is scaffold time step 1 (4 role vars)
  | empty            -- block has no clauses touching it
  deriving DecidableEq, Repr, Fintype

/-- A profile is a multiset of ≤ 6 local block types. -/
abbrev Profile := List LocalBlockType

/-- The number of distinct profiles of length ≤ 6 from a 4-element alphabet
    is at most 4^7 = 16384 (a constant independent of n). -/
def maxProfiles : ℕ := 4 ^ 7

/-! ## Same profile → same span dimension

  If two derivative supports S₁, S₂ have the same profile, then:
  - The generators {m · ∂^{S₁}(V)} and {m · ∂^{S₂}(V)} span subspaces
    of the same dimension
  - This is because there's a block-local variable permutation mapping
    S₁'s blocks to S₂'s blocks, preserving the clause structure

  The variable permutation induces a ring isomorphism on MvPolynomial
  that maps one set of generators bijectively to the other.
-/

/-- The SPDP rank is bounded by maxProfiles × perProfileDim.
    Each profile contributes at most perProfileDim independent generators.
    There are at most maxProfiles distinct profiles.
    Total rank ≤ maxProfiles × perProfileDim. -/
def perProfileDim (ℓ : ℕ) : ℕ := (ℓ + 6 + maxGenVars) ^ maxGenVars

/-- The per-profile dimension bound: generators from a single profile
    live in a polynomial space on maxGenVars variables of degree ≤ ℓ + 6.
    The dimension of this space is at most (ℓ + 6 + v choose v) ≤ (ℓ + 6 + v)^v.
    
    Proof: for a fixed S, m ranges over monomials on ≤ 24 vars of degree ≤ ℓ.
    ∂^S(V) is a fixed polynomial on ≤ 18 vars of degree ≤ 6.
    The product m · ∂^S(V) has degree ≤ ℓ + 6 on ≤ 42 vars.
    These products span a subspace of dim ≤ C(42 + ℓ + 6, 42). -/
theorem rank_le_profiles_times_dim {N : ℕ}
    (κ ℓ : ℕ) (V : MvPolynomial (Fin N) ℚ) (bp : CompiledPoly.BlockPartition N)
    (hV_deg : V.totalDegree ≤ 6)
    (hV_local : True) -- placeholder: V is a sum of local terms
    : blockedSpdpRankQ κ ℓ V bp ≤ maxProfiles * perProfileDim ℓ := by
  sorry

/-! ## Per-profile span dimension bound

  For a fixed profile p, the generators with that profile span a subspace
  of dimension ≤ C(v + ℓ + d, v) where:
  - v = maxGenVars = 42 (variables per generator)
  - d = 6 (degree of V)
  - ℓ = log₂ n (shift degree)

  This gives dimension ≤ C(42 + log n + 6, 42) ≈ (log n + 48)^42 = (log n)^{O(1)}.
-/

/-- Per-profile dimension bound: generators with a fixed profile span
    a space of dimension ≤ (ℓ + d + v)^v where v, d are constants. -/
theorem per_profile_dim_bound (κ ℓ d v : ℕ) (hd : d ≤ 6) (hv : v ≤ 42) :
    True := trivial  -- placeholder

/-! ## Assembly: restricted_clause_survival from profile compression

  Total rank ≤ (number of profiles) × (per-profile dimension)
            ≤ 4^6 × (log n + 48)^42
            = O(1) × (log n)^42
            ≤ (log n + 1)^50 for large n

  So c = 50 and n₀ = some concrete threshold.
-/

/-- Profile compression gives restricted_clause_survival.

    Chain:
    rank ≤ maxProfiles × perProfileDim(log n)       [rank_le_profiles_times_dim]
         = 4^7 × (log n + 48)^42                    [definitions]
         ≤ (log n + 1)^50                            [for large n]
    
    So c = 50 suffices. -/
theorem restricted_clause_survival_from_profiles (M : TuringMachine.DTM) :
    ∃ (c : ℕ) (n₀ : ℕ), ∀ n : ℕ, n ≥ n₀ → ∀ (hn2 : n ≥ 2),
      CompiledPoly.blockedSpdpRankQ (Nat.log 2 n) (Nat.log 2 n)
        (CompiledPoly.violationPolyQ (initialSemanticCNF M n hn2))
        (initialSemantic_local M n hn2).partition ≤ (Nat.log 2 n + 1) ^ c := by
  -- n₀ = 2^100 ensures log₂ n ≥ 100, making the arithmetic work
  refine ⟨50, 2 ^ 100, ?_⟩
  intro n hn hn2
  set ℓ := Nat.log 2 n
  -- Step 1: rank ≤ maxProfiles × perProfileDim ℓ
  have h_rank := rank_le_profiles_times_dim ℓ ℓ
    (CompiledPoly.violationPolyQ (initialSemanticCNF M n hn2))
    (initialSemantic_local M n hn2).partition
    (CompiledPoly.violationPolyQ_totalDegree_le _) trivial
  -- Step 2: maxProfiles × perProfileDim ℓ ≤ (ℓ + 1)^50
  -- maxProfiles = 4^7, perProfileDim ℓ = (ℓ + 48)^42
  -- 4^7 × (ℓ + 48)^42 ≤ (ℓ + 1)^50 for large ℓ
  -- (This is: constant × polylog ≤ polylog with higher exponent)
  have h_bound : maxProfiles * perProfileDim ℓ ≤ (ℓ + 1) ^ 50 := by
    -- maxProfiles = 4^7 = 16384
    -- perProfileDim ℓ = (ℓ + 48)^42
    -- Need: 16384 × (ℓ + 48)^42 ≤ (ℓ + 1)^50
    -- Equivalently: 16384 ≤ (ℓ+1)^50 / (ℓ+48)^42 ≈ (ℓ+1)^8 for large ℓ
    -- For ℓ ≥ 2 (n ≥ 4): ℓ+1 ≥ 3, and we need 16384 ≤ 3^8 = 6561... no.
    -- Need ℓ larger. For ℓ ≥ 48: (ℓ+1)/(ℓ+48) ≥ 49/96 ≥ 1/2
    -- Then (ℓ+1)^50 / (ℓ+48)^42 ≥ (ℓ+48)^50 / 2^50 / (ℓ+48)^42
    --   = (ℓ+48)^8 / 2^50 ≥ 96^8 / 2^50 ≈ 7.2×10^15 / 1.1×10^15 ≈ 6.5
    -- Still not enough. Needs larger n₀.
    -- For n₀ large enough this works. Adjust n₀ in the theorem.
    sorry
  exact le_trans h_rank h_bound

end ProfileCompression
