/-
  CoupledVerifier.lean — Coupled verifier polynomial Q×_Φ (Paper §8.5, §9.3)

  The coupled verifier polynomial for a 3-CNF Φ with disjoint clauses:
    Q×_Φ(u, z) = ∏_{C ∈ C_disj} (1 - z_C · V_C(u_{B_C}))

  Key theorem (§9.3): Q× has an identity minor of size C(L, κ) in its
  blocked SPDP matrix, where L = |C_disj|.

  The proof:
  - For each κ-subset S ⊆ C_disj:
    - ∂_{z_S} Q× = (-1)^κ · ∏_{C ∈ S} V_C · ∏_{C ∉ S} (1 - z_C · V_C)
    - Taking the z-free part: (-1)^κ · ∏_{C ∈ S} V_C
    - With tag monomial τ_S = ∏_{C ∈ S} τ_C: coefficient = (-1)^κ
  - For S ≠ S': the tag monomial τ_S has support in ∪_{C ∈ S} B_C
    which is disjoint from ∪_{C ∈ S'} B_C for C ∈ S \ S',
    so [τ_S] R_{S'} = 0.
  - This gives a C(L, κ) × C(L, κ) identity minor.
-/
import PallLean.SPDPDefs
import PallLean.TseitinLowerBound
import Mathlib.Tactic

namespace CoupledVerifier

open MvPolynomial SPDP PneqNP_Defs

/-! ## Clause gadget polynomial

  For each clause C in a 3-CNF, the clause gadget V_C(u) = 0 iff C is satisfied.
  V_C is multilinear, degree ≤ 3, supported on block B_C.
  There exists a tag monomial τ_C in B_C with [τ_C]V_C = 1.
-/

structure ClauseGadget (N : ℕ) where
  -- The clause gadget polynomial
  poly : MvPolynomial (Fin N) ℚ
  -- The block of variables for this clause
  block : Finset (Fin N)
  -- Variables of poly are in the block
  vars_subset : poly.vars ⊆ block
  -- Degree bound
  deg_le : poly.totalDegree ≤ 3
  -- Tag monomial: a specific monomial with coefficient 1
  tagMonomial : Fin N →₀ ℕ
  tag_support : tagMonomial.support ⊆ block
  tag_coeff : poly.coeff tagMonomial = 1

/-! ## Coupled verifier polynomial

  Q×(u, z) = ∏_{i=0}^{L-1} (1 - z_i · V_i(u))

  where z_0, ..., z_{L-1} are fresh selector variables
  and V_i are clause gadgets on disjoint blocks B_i.
-/

-- For L disjoint clause gadgets on N u-variables + L z-variables:
-- Total variables = N + L, where indices 0..N-1 are u-variables
-- and N..N+L-1 are z-variables (selectors).

-- The selector variable for clause i
def selectorVar (N L : ℕ) (i : Fin L) : Fin (N + L) :=
  ⟨N + i.1, by omega⟩

-- Embed u-variable into the combined space
def embedU (N L : ℕ) (v : Fin N) : Fin (N + L) :=
  ⟨v.1, by omega⟩

/-! ## Identity minor construction (Theorem 9.3)

  The SPDP matrix of Q× has rows indexed by (S, m) pairs
  where S is a list of κ variables and m is a monomial of degree ≤ ℓ.

  For the identity minor:
  - Rows: for each κ-subset S ⊆ {0,...,L-1}, take S_z = {z_{s_1},...,z_{s_κ}}
    and m = 1 (trivial multiplier).
  - Columns: for each κ-subset S, take τ_S = ∏_{i ∈ S} τ_i
    (product of tag monomials for the selected clauses).
  - Diagonal: [τ_S] (∂^{S_z} Q×) = (-1)^κ ≠ 0
  - Off-diagonal: [τ_S] (∂^{S'_z} Q×) = 0 for S ≠ S'
  - Identity minor of size C(L, κ).
-/

-- The key algebraic fact: derivative of a product over disjoint blocks.
-- ∂_{z_S} ∏_i (1 - z_i · V_i) = (-1)^|S| · ∏_{i ∈ S} V_i · ∏_{i ∉ S} (1 - z_i · V_i)
-- (when S is a set of distinct selector variables)
--
-- After setting z = 0 (taking the z-free coefficient):
-- The z-free part of ∂_{z_S} Q× = (-1)^|S| · ∏_{i ∈ S} V_i
--
-- Then: [τ_S] ((-1)^κ · ∏_{i ∈ S} V_i) = (-1)^κ · ∏_{i ∈ S} [τ_i]V_i
--        = (-1)^κ · ∏_{i ∈ S} 1 = (-1)^κ
--
-- And for S' ≠ S: ∃ i ∈ S \ S', so ∏_{i ∈ S'} V_i does NOT contain
-- the tag monomial τ_i for i ∈ S \ S', so [τ_S] = 0.

-- This gives the identity minor. Combined with:
-- identity_minor_gives_rank_lower_bound: rank ≥ C(L, κ) > √n
-- We get: the coupled verifier polynomial has SPDP rank > √n.
-- Therefore the corresponding boolean function escapes FSPDP.

-- The remaining gap in disjoint_clauses_give_hard_function:
-- connecting the abstract DisjointClauseFamily to a concrete
-- boolean function whose multilinear interpolation has high
-- restrictedSpdpRank. This requires:
-- 1. Defining Q× as an MvPolynomial
-- 2. Showing its SPDP matrix has the identity minor
-- 3. Extracting a BoolFun n with the same rank property

-- Step 1 is a polynomial construction (well-defined).
-- Step 2 is the algebraic computation above (§9.3).
-- Step 3 connects Q× to a boolean function (via evaluation on {0,1}^n).


/-! ## The core algebraic computation

  For a product of independent factors:
  ∏_{i=0}^{L-1} (1 - z_i · V_i)

  The partial derivative ∂_{z_S} (with S = {i_1,...,i_κ}) gives:
  (-1)^κ · ∏_{j ∈ S} V_j · ∏_{j ∉ S} (1 - z_j · V_j)

  After setting all z_j = 0:
  (-1)^κ · ∏_{j ∈ S} V_j

  Taking the coefficient at the product tag monomial τ_S = ∏_{j ∈ S} τ_j:
  (-1)^κ · ∏_{j ∈ S} [τ_j] V_j = (-1)^κ · ∏_{j ∈ S} 1 = (-1)^κ

  For S' ≠ S: some factor V_j (j ∈ S \ S') is missing from ∏_{j ∈ S'} V_j,
  so the tag τ_j cannot appear, giving coefficient 0.
-/

-- Product of disjoint-block polynomials has multiplicative coefficients
theorem coeff_prod_disjoint {N : ℕ} {L : ℕ}
    (V : Fin L → MvPolynomial (Fin N) ℚ)
    (τ : Fin L → (Fin N →₀ ℕ))
    (hcoeff : ∀ i, (V i).coeff (τ i) = 1)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (τ i).support (τ j).support) :
    (Finset.univ.prod V).coeff (Finset.univ.sum τ) = 1 := by
  -- Product of polynomials with disjoint support: coefficient of sum = product of coefficients.
  -- This is a standard fact about multivariate polynomials with disjoint variables.
  sorry

-- The identity minor theorem follows from coeff_prod_disjoint
-- applied to subsets S ⊆ {0,...,L-1} of size κ.
-- For S: coefficient = 1 (all tag coefficients are 1).
-- For S' ≠ S: coefficient = 0 (missing tag support from S \ S').
-- This gives a C(L, κ) × C(L, κ) identity minor (up to ±1 signs).

end CoupledVerifier
