/-
Copyright (c) 2026 Darren Edwards. All rights reserved.
Released under Apache 2.0 license.
-/
import PallLean.MultilinearSPDP

/-!
# Profile Compression for Tseitin SPDP Rank (§9)

Goal: prove `tseitin_spdp_rank_bound`:
  mlBlockedSpdpRank (tseitinPartition n) κ κ (tseitinPoly ℚ n) ≤ n^10
for AdmissibleSpdpParams n κ (i.e., κ ≥ 5, κ ≤ log₂ n).

## Proof Architecture (7 Lemmas)

### Layer 1 — Structure (already proved in IdentityMinor.lean)
- `coupledVerifier_eq_prod`: tseitinPoly = ∏ cvFactor
- `pderiv_cvFactor_eq`: ∂_{z_c}(cvFactor c) = -clauseGadget c
- `pderiv_cvFactor_ne`: ∂_{z_c}(cvFactor d) = 0 for c ≠ d
- `iterDeriv_cvProd_eq`: multi-selector derivative factorization

### Layer 2 — Canonical Windows
Block-admissible derivative lists for tseitinPartition are (essentially)
lists of distinct selector variables. Every SPDP generator reduces to
a canonical selector window form.

### Layer 3 — Live Interfaces
After hitting κ selectors, the derivative depends only on a bounded
neighborhood of the hit clauses. The number of "live interfaces" is
O(κ) = O(log n).

### Layer 4 — Profile Histograms
Windows are classified by their interface-type histogram. The number
of realizable profiles is polynomial in n.

### Layer 5 — Within-Profile Dimension
Rows sharing a profile lie in a bounded-dimensional subspace.

### Layer 6 — Assembly
Sum dimensions over profiles to get the polynomial rank bound.
-/

namespace SPDP

open MvPolynomial Finset IdentityMinor Tseitin MultilinearSPDP NPWitness

-- ============================================================
-- §1. Abbreviations and key structural facts
-- ============================================================

/-- Short name for the Tseitin formula at parameter n -/
noncomputable abbrev Φn (n : ℕ) := tseitinAt n

/-- Number of clauses in the n-th Tseitin formula -/
noncomputable abbrev numClausesAt (n : ℕ) := (Φn n).clauses.length

/-- The clause factor (1 - z_c · gadget_c) for the n-th formula -/
noncomputable abbrev cvFactorAt (n : ℕ) (c : Fin (numClausesAt n)) :
    MvPolynomial (Fin (npNumVars n)) ℚ :=
  IdentityMinor.cvFactor ℚ (Φn n) c

/-- The clause gadget for clause c -/
noncomputable abbrev clauseGadgetAt (n : ℕ) (c : Fin (numClausesAt n)) :
    MvPolynomial (Fin (npNumVars n)) ℚ :=
  clauseGadget ℚ (Φn n) c

/-- Selector variable index for clause c -/
noncomputable abbrev selectorAt (n : ℕ) (c : Fin (numClausesAt n)) :
    Fin (npNumVars n) :=
  selectorIdx (Φn n) c

-- ============================================================
-- §2. Canonical Selector Windows
-- ============================================================

/-! ### Block structure of tseitinPartition

Key fact: In `tseitinPartition`, selector z_c is in block (c+1),
and ALL non-selector variables are in block 0.

Consequence: A block-admissible list of length κ can contain at most
ONE non-selector variable (from block 0). The remaining κ-1 (or all κ)
elements must be distinct selectors from distinct blocks.

For the rank bound, we can focus on pure-selector derivative lists,
since mixing in a block-0 variable only reduces the available
selector diversity (fewer distinct blocks). -/

/-- A canonical selector window: a set of κ distinct clauses whose
    selectors form a block-admissible derivative list. -/
structure CanonicalWindow (n κ : ℕ) where
  /-- The hit clause indices -/
  hitClauses : Finset (Fin (numClausesAt n))
  /-- Exactly κ clauses hit -/
  card_eq : hitClauses.card = κ

/-- The selector derivative list for a canonical window -/
noncomputable def CanonicalWindow.selectorList {n κ : ℕ}
    (w : CanonicalWindow n κ) : List (Fin (npNumVars n)) :=
  (w.hitClauses.val.toList).map (selectorAt n)

/-- The SPDP generator from a canonical window with shift monomial m:
    mlProj(m · iterDerivList(selectors, tseitinPoly)) -/
noncomputable def canonicalGenerator {n κ : ℕ}
    (w : CanonicalWindow n κ)
    (m : MvPolynomial (Fin (npNumVars n)) ℚ) :
    MvPolynomial (Fin (npNumVars n)) ℚ :=
  mlProj (m * iterDerivList w.selectorList (tseitinPoly ℚ n))

/-! ### Reduction to canonical windows

Every mlBlockedSpdpSubspace generator for tseitinPartition can be
expressed as a linear combination of canonical generators.

The key insight: block-admissible lists for tseitinPartition have
elements from distinct blocks. Since block 0 contains all non-selectors
and blocks 1..m contain one selector each, at most one element is
non-selector. The non-selector derivative either:
(a) hits a clause variable appearing in some gadget → bounded contribution
(b) hits nothing in the product → zero

In either case, the resulting generator lies in the span of canonical
(pure-selector) generators with slightly modified shift monomials. -/

/-- The subspace spanned by canonical window generators -/
noncomputable def canonicalSubspace (n κ : ℕ) :
    Submodule ℚ (MvPolynomial (Fin (npNumVars n)) ℚ) :=
  Submodule.span ℚ
    { q | ∃ (w : CanonicalWindow n κ)
            (m : MvPolynomial (Fin (npNumVars n)) ℚ),
        m.totalDegree ≤ κ ∧
        m.vars ⊆ w.selectorList.toFinset ∧
        q = canonicalGenerator w m }

/-- Every SPDP generator for tseitinPartition is in the canonical subspace.
    This reduces the rank bound to bounding the canonical subspace dimension. -/
theorem spdp_subspace_le_canonical (n κ : ℕ)
    (hparam : AdmissibleSpdpParams n κ) :
    mlBlockedSpdpSubspace (tseitinPartition n) κ κ (tseitinPoly ℚ n) ≤
    canonicalSubspace n κ := by
  sorry

-- ============================================================
-- §3. Factored Form of Canonical Generators
-- ============================================================

/-! ### Using iterDeriv_cvProd_eq

From IdentityMinor.lean, we have:
  iterDerivList (ks.map selectorIdx) (∏ cvFactor) =
    C((-1)^|ks|) * (ks.map clauseGadget).prod * (univ \ ks.toFinset).prod cvFactor

So a canonical generator with hit set C and shift m becomes:
  mlProj(m · C((-1)^κ) · ∏_{c∈C} gadget_c · ∏_{c∉C} factor_c)

The ∏_{c∉C} factor_c is the "unhit product" — the object that must be
compressed by locality/profile structure. -/

/-- The "hit gadget product" for a window -/
noncomputable def hitGadgetProd {n κ : ℕ} (w : CanonicalWindow n κ) :
    MvPolynomial (Fin (npNumVars n)) ℚ :=
  w.hitClauses.prod (clauseGadgetAt n)

/-- The "unhit factor product" for a window -/
noncomputable def unhitFactorProd {n κ : ℕ} (w : CanonicalWindow n κ) :
    MvPolynomial (Fin (npNumVars n)) ℚ :=
  (Finset.univ \ w.hitClauses).prod (cvFactorAt n)

-- ============================================================
-- §4. Live Interfaces and Boundary Reduction
-- ============================================================

/-! ### The compression mechanism

The unhit product ∏_{c∉C} (1 - z_c · gadget_c) involves all m-κ
remaining clauses. Naively this is exponentially rich.

But after multilinear projection, only variables that appear in BOTH
the hit gadgets AND the unhit factors contribute non-trivially.
These shared variables form the "live interfaces."

For 3-SAT with bounded occurrence (each variable in ≤ O(1) clauses),
each hit clause c shares variables with at most O(1) neighboring
clauses. So the total number of "live" unhit clauses is O(κ).

The unhit clauses that share NO variables with any hit clause
contribute a factor that is independent of the hit set, and hence
contributes the same subspace for every window. This factor can
be absorbed into the profile machinery. -/

/-- Clauses neighboring the hit set: share at least one variable -/
noncomputable def neighborClauses {n κ : ℕ} (w : CanonicalWindow n κ) :
    Finset (Fin (numClausesAt n)) :=
  (Finset.univ \ w.hitClauses).filter (fun d =>
    ∃ c ∈ w.hitClauses, ∃ v,
      v ∈ clauseVarSet (tseitinAt n) c ∧ v ∈ clauseVarSet (tseitinAt n) d)

/-- Each hit clause neighbors at most O(1) other clauses.
    For degree-3 regular graphs with bounded occurrence, this is ≤ 9. -/
theorem neighbor_clauses_card_le {n κ : ℕ} (w : CanonicalWindow n κ)
    (hn : n ≥ 4) :
    (neighborClauses w).card ≤ 9 * κ := by
  sorry

-- ============================================================
-- §5. Profile Histograms
-- ============================================================

/-! ### Local clause types

In the Tseitin construction, every clause gadget has the same
algebraic form: a product/sum of 3 literal polynomials.
The "type" of a clause relative to a hit set is determined by
how many of its variables are shared with hit clauses.

Since each clause has exactly 3 variables, the type is one of:
  0 shared, 1 shared, 2 shared, or 3 shared
giving |Σ| = 4 local types. -/

/-- Local interface type: number of variables shared with the hit set.
    For 3-SAT, this is 0, 1, 2, or 3. -/
abbrev LocalInterfaceType := Fin 4

/-- Profile histogram: for each local type, how many unhit neighbors
    have that type. -/
abbrev ProfileHist := LocalInterfaceType → ℕ

/-- The profile of a canonical window: histogram of neighbor types -/
noncomputable def windowProfile {n κ : ℕ} (w : CanonicalWindow n κ) :
    ProfileHist :=
  fun τ => ((neighborClauses w).filter (fun d =>
    -- Count shared variables between d and the hit set
    (Finset.univ.filter (fun c =>
      c ∈ w.hitClauses ∧
      ∃ v, v ∈ clauseVarSet (tseitinAt n) c ∧ v ∈ clauseVarSet (tseitinAt n) d
    )).card = τ.val
  )).card

/-- Total mass of a profile is at most the number of neighbors -/
theorem profile_total_mass_le {n κ : ℕ} (w : CanonicalWindow n κ)
    (hn : n ≥ 4) :
    ∑ τ : LocalInterfaceType, windowProfile w τ ≤ 9 * κ := by
  sorry

/-- Number of realizable profiles with total mass ≤ R.
    Stars-and-bars: histograms over 4 types with total ≤ R
    have at most (R+1)^4 possibilities (each coordinate ∈ {0,...,R}). -/
theorem num_profiles_le (R : ℕ)
    (S : Finset ProfileHist) (hS : ∀ h ∈ S, ∑ τ, h τ ≤ R) :
    S.card ≤ (R + 1) ^ 4 := by
  sorry

-- ============================================================
-- §6. Within-Profile Subspace Dimension
-- ============================================================

/-! ### Per-profile dimension bound

For each profile h, the generators from windows with that profile
lie in a subspace of dimension at most ∏_τ C(h(τ) + d_τ, d_τ)
where d_τ is the local derivative space dimension for type τ.

From TypeDecomp.lean: `localDerivSpace_finrank_le_16` gives d_τ ≤ 16
for width-4 clause gadgets.

The key structural insight: after fixing the profile, the only
degrees of freedom are:
1. Which specific clauses of each type are "active" (absorbed by profile)
2. The local derivative space contribution per active clause (dim ≤ 16)
3. The shift monomial (degree ≤ κ, support ⊆ hit selectors)

The shift monomial contributes at most C(κ + κ, κ) ≤ (2κ)^κ ≤ n
additional dimensions (since κ ≤ log₂ n).

Total per-profile dimension: ≤ 16^κ · n ≤ n · n^4 = n^5
(using 16^κ ≤ 16^(log₂ n) = n^4).
-/

/-- Per-profile dimension bound.
    For a fixed profile h with total mass R ≤ 9κ,
    the subspace of generators with that profile has dimension
    at most n^5. -/
theorem within_profile_dim_le (n κ : ℕ)
    (hparam : AdmissibleSpdpParams n κ)
    (h : ProfileHist) (hR : ∑ τ, h τ ≤ 9 * κ) :
    -- The subspace of generators from windows with profile h
    -- has finrank ≤ n^5
    True := by  -- placeholder for the real statement
  trivial

-- ============================================================
-- §7. Assembly: Sum Over Profiles
-- ============================================================

/-! ### Putting it all together

Total rank ≤ (number of profiles) × (per-profile dimension)
         ≤ (9κ + 1)^4 × n^5
         ≤ (9 log₂ n + 1)^4 × n^5
         ≤ n^5 × n^4       (for n ≥ 16, since (9 log n + 1)^4 ≤ n^4)
         ≤ n^9
         ≤ n^10

This gives the final bound matching the axiom. -/

/-- The assembly arithmetic: profile count × per-profile dim ≤ n^10 -/
theorem assembly_arithmetic (n κ : ℕ) (hn : n ≥ 16)
    (hκ : κ ≤ Nat.log 2 n) :
    (9 * κ + 1) ^ 4 * n ^ 5 ≤ n ^ 10 := by
  sorry

/-! ### Main theorem (target: replace the axiom)

Once all layers are proved, this replaces `tseitin_spdp_rank_bound`. -/

-- theorem tseitin_spdp_rank_bound_proved (n : ℕ) (hn : n ≥ 4)
--     (κ : ℕ) (hparam : AdmissibleSpdpParams n κ) :
--     mlBlockedSpdpRank (tseitinPartition n) κ κ (tseitinPoly ℚ n) ≤ n ^ 10 := by
--   sorry

end SPDP
