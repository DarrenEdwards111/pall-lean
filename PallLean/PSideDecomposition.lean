/-
  PSideDecomposition.lean — Decomposition of restricted_clause_survival

  The P-side collapse axiom decomposes into:
  1. Degree truncation: only |S| ≤ deg(V) contributes (PROVED in DegreeDrop)
  2. S-coupled variable locality: generators use O(1) variables per S
  3. Per-S span dimension: ≤ (ℓ + deg V)^{O(1)} per generator family
  4. Profile compression: distinct profiles ≤ R^{O(1)} where R = polylog(n)

  Sub-lemma 4 is the core of the paper's §5 profile compression argument.
  Sub-lemmas 1-3 give a polynomial bound; sub-lemma 4 refines to polylog.
-/
import PallLean.CompiledPoly
import PallLean.CookLevin
import PallLean.DegreeDrop
import Mathlib.Tactic

namespace PSideDecomposition

open MvPolynomial CompiledPoly CookLevin SPDP

/-! ## Sub-lemma 1: Degree truncation (PROVED)

  For V with totalDegree ≤ d, any generator m · ∂^S(V) with |S| > d
  has ∂^S(V) = 0, so the generator is 0.
  
  Therefore, blockedSpdpRankQ only depends on |S| ≤ d generators.
  For our V: d ≤ 6.
-/

-- Already proved: SPDP.iterDerivList_eq_zero_of_length_gt
-- Already proved: CompiledPoly.violationPolyQ_totalDegree_le

/-! ## Sub-lemma 2: S-coupled variable locality

  With the cell partition (n+2 blocks, ≤ 4 vars/block) and S-coupling:
  - S has |S| ≤ 6, touching ≤ 6 blocks
  - m's variables lie in S-touched blocks: ≤ 6 × 4 = 24 variables
  - ∂^S(V) has the same variables as V (derivatives don't add new variables)
  - But m · ∂^S(V) has variables from both m and ∂^S(V)
  
  Key: the RANK depends on how many linearly independent generators
  there are, not on the ambient variable count.
-/

/-- The number of block-admissible (S, m) pairs with |S| ≤ d, deg(m) ≤ ℓ,
    S a transversal, and m S-coupled, is bounded by:
    C(r, d) × C(d × blockSize + ℓ, ℓ) where r = numBlocks.
    
    For our cell partition: r = n+2, d = 6, blockSize = 4, ℓ = log n.
    Count ≤ C(n+2, 6) × C(24 + log n, log n) ≈ n^6 × (log n)^24.
    
    This is polynomial in n — a §4.2 bound, not polylog. -/
theorem generator_count_polynomial (N κ ℓ d : ℕ) (bp : CompiledPoly.BlockPartition N) :
    True := trivial  -- placeholder for the counting lemma

/-! ## Sub-lemma 3: Per-generator-family span dimension

  For a fixed S (|S| ≤ 6), the generators {m · ∂^S(V) : m S-coupled, deg m ≤ ℓ}
  span a subspace of dimension ≤ C(v + ℓ + d, ℓ + d) where:
  - v = number of variables in S-touched blocks (≤ 24)
  - d = deg(V) (≤ 6)
  - ℓ = shift degree bound (= log n)
  
  This is because m · ∂^S(V) has degree ≤ ℓ + d and uses ≤ v + 6 variables.
  The polynomial space on v variables of degree ≤ ℓ+d has dimension C(v+ℓ+d, ℓ+d).
  
  For v = 24, d = 6, ℓ = log n: C(30 + log n, log n + 6) ≈ (log n + 30)^30.
  This IS polylogarithmic! (log n)^{O(1)}.
  
  BUT: different S choices yield different variable sets, so the total
  rank is the SUM over distinct S families — which is polynomial, not polylog.
-/

/-- For a FIXED derivative set S, the generators span a space of dimension
    ≤ (ℓ + d + v)^v where v = |vars in S-touched blocks| and d = deg(V). -/
theorem per_S_span_dimension_bound : True := trivial  -- placeholder

/-! ## Sub-lemma 4: Profile compression (Paper §5)

  The key insight: many different S choices are "algebraically equivalent"
  in the sense that they produce the same row subspace (up to relabeling).
  
  An interface-anonymous PROFILE is a histogram h : T → {0,...,R} where
  T is the finite type alphabet (|T| = O(1)) and R is the window width.
  
  Lemma 5.7 (Profile compression removes κ-dependence):
  The number of distinct profiles is bounded by |H(R)| ≤ R^{O(1)}
  independent of κ.
  
  With R = polylog(n): |H| = polylog(n).
  
  Combined with per-profile dimension ≤ poly(n) (from sub-lemma 3):
  Total rank ≤ |H| × per-profile-dim = polylog(n) × poly(n).
  
  Wait — that's still polynomial. The paper's Theorem 5.16 says the
  per-profile dimension is R^{O(1)} (not poly(n)), giving:
  Total rank ≤ R^{O(1)} × R^{O(1)} = R^{O(1)} = polylog(n).
  
  The per-profile dimension bound comes from the locality structure:
  within a single profile, all generators lie in a space determined by
  the profile's interface configuration, which has dimension R^{O(1)}.
-/

/-- Profile compression: the number of distinct interface-anonymous
    profiles is bounded by R^{O(1)} where R is the window width. -/
axiom profile_count_polylog (M : TuringMachine.DTM) (n : ℕ) (hn2 : n ≥ 2) :
    True  -- placeholder for the profile counting bound

/-- Per-profile span dimension: within a single profile, the SPDP
    row subspace has dimension ≤ R^{O(1)}. -/
axiom per_profile_dim_polylog (M : TuringMachine.DTM) (n : ℕ) (hn2 : n ≥ 2) :
    True  -- placeholder for per-profile dimension bound

/-! ## Assembly: restricted_clause_survival from sub-lemmas

  Total rank = Σ_{profiles h} dim(V_h)
             ≤ |H(R)| × max_h dim(V_h)
             ≤ R^{O(1)} × R^{O(1)}
             = R^{O(1)}
             = (log n)^{O(1)}
             
  This is exactly restricted_clause_survival with c = O(1).
-/

end PSideDecomposition
