/-
  NPSideProof.lean — Proof roadmap for hard_np_family_exists

  Paper reference: Theorem 10.1 (Tseitin SPDP rank lower bound)
  + trivial NP membership of 3-SAT

  The claim: ∃ F ∈ NP, ¬InFSPDP(F n) for large n

  Proof decomposition:
  (1) Define F = 3-SAT decision function
  (2) 3-SAT ∈ NP (witness = satisfying assignment)
  (3) Tseitin formulas Φ_n on expander graphs (explicit construction)
  (4) The coupled verifier polynomial Q×_Φ contains a permanent minor
      (paper Theorem 10.1, via identity-minor argument)
  (5) Permanent SPDP rank ≥ m+1 (proved in v1: PermanentLower.lean)
  (6) Therefore Q×_Φ rank ≥ n^Θ(log n) > √n
  (7) 3-SAT evaluated on Tseitin instances escapes FSPDP
  (8) Package as hard_np_family_exists

  Step (5) is proved. Steps (2)+(8) are packaging.
  Steps (3)+(4) are the core: Tseitin → permanent embedding.
  Step (6) follows from (4)+(5).
-/
import PallLean.PneqNP_Defs
import PallLean.Permanent
import PallLean.PermanentLower
import Mathlib.Tactic

namespace NPSideProof

open PneqNP_Defs

/-! ## Step (5): Permanent lower bound — PROVED

  permanentSpdpRank m ≥ m + 1
  This is in PermanentLower.lean. -/

-- Already proved: PermanentLower.permanent_spdp_rank_lb

/-! ## Step (3): Tseitin formulas — explicit construction

  Tseitin formula Φ_n on an expander graph G_n:
  - n edges → n Boolean variables
  - For each vertex v: XOR constraint on incident edges
  - Parity bits chosen so Φ_n is unsatisfiable
  - Each variable in O(1) clauses (bounded occurrence)
  - m = Θ(n) clauses

  These are explicit 3-CNFs, uniformly constructible in poly(n) time. -/

-- For the formalization: we don't need the full Tseitin construction.
-- We need: ∃ a 3-CNF family with the right SPDP rank lower bound.
-- The permanent lower bound provides the rank.
-- The Tseitin construction provides the specific formula.

/-! ## Step (4): Tseitin → permanent embedding

  The coupled verifier polynomial Q×_Φ for Tseitin Φ_n
  contains the permanent as a sub-polynomial.

  The argument (paper §8-10):
  - Q×_Φ = Π_C (clause polynomial for C)
  - The clause polynomials for Tseitin have a specific tensor structure
  - This tensor structure contains an identity minor of the permanent
  - Therefore rank(Q×_Φ) ≥ permanentSpdpRank(√n) ≥ √n + 1

  This is the deepest single theorem in the paper.
  It connects combinatorial graph structure (Tseitin on expanders)
  to algebraic structure (permanent polynomial).
-/

-- The core lemma: Tseitin's coupled verifier polynomial has high rank
-- This would be: ∀ large n, restrictedSpdpRank(Q×_{Φ_n}) ≥ √n + 1

/-! ## Step (2): 3-SAT ∈ NP — trivial

  The verifier V receives (formula_encoding x, assignment w).
  V checks that w satisfies all clauses of the formula encoded by x.
  This is computable in O(|x| + |w|) time.

  For UniformNP: k = 1 (witness length = n^1 = n),
  V(n + n^1)(append x w) checks satisfaction. -/

-- To prove sat_in_NP formally, we need:
-- 1. Define the 3-SAT function family
-- 2. Define the verifier function family
-- 3. Construct a DTM that computes the verifier
-- 4. Prove the DTM is correct and runs in poly-time
--
-- The DTM construction is the bottleneck (formalizing tape machine execution).
-- For the paper-faithful formalization, this is standard CS but tedious in Lean.

end NPSideProof
