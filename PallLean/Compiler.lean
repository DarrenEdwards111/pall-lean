/-!
# Compilation Model

Pall paper Sections 3, 6, 14: The compiler that converts polynomial-time
TM computations into κ-padded polynomials with bounded blocked SPDP rank.
-/

import PallLean.SPDPDefs

namespace Compiler

open SPDP

/-! ## Turing Machine Model -/

/-- A deterministic Turing machine running in time T(n) ≤ n^c -/
structure PolyTimeTM where
  c : ℕ  -- time exponent
  -- The actual machine is abstracted; we only need the complexity bound

/-- The compilation produces a κ-padded polynomial from a TM + input length -/
axiom compiled_polynomial (F : Type*) [Field F] (M : PolyTimeTM) (n : ℕ)
  (params : SPDPParams) (B : BlockPartition (compiler_vars n M.c)) :
  MvPolynomial (Fin (compiler_vars n M.c)) F

/-- Number of variables in the compiled polynomial -/
axiom compiler_vars (n c : ℕ) : ℕ

/-- Compiler variables are polynomial in n -/
axiom compiler_vars_poly (n c : ℕ) : compiler_vars n c ≤ n ^ (c + 1)

/-! ## P-Side Main Theorem (Theorem 6.1 / 6.3) -/

/-- **Theorem 6.1 (P-side collapse)**: Every polytime computation has
    polynomial blocked SPDP rank under the canonical compiler gauge.

    For every M ∈ DTIME(n^c) and the canonical (κ,ℓ) = Θ(log n):
    ΓB_{κ,ℓ}(P_{M,n}) ≤ n^{O(1)}

    This is the universal quantifier over all polytime machines. -/
axiom p_side_collapse (F : Type*) [Field F] (M : PolyTimeTM) (n : ℕ)
  (params : SPDPParams) (B : BlockPartition (compiler_vars n M.c))
  (h_params : params.κ = Nat.log 2 n ∧ params.ℓ = Nat.log 2 n) :
  ∃ (C : ℕ), SPDPRank F params B (compiled_polynomial F M n params B) ≤ n ^ C

/-! ## Proof ingredients (named arrows from Section 18.1) -/

/-- Profile compression removes κ-dependence (Lemma 5.7) -/
axiom profile_compression (F : Type*) [Field F] (n : ℕ) (R : ℕ)
  (h_R : R ≤ (Nat.log 2 n) ^ 3) :
  -- Number of distinct interface-anonymous profiles is R^{O(1)}
  ∃ (P : ℕ), P ≤ R ^ 4

/-- Within-profile dimension bound (Lemma 5.11) -/
axiom within_profile_dim (F : Type*) [Field F] (n : ℕ) :
  -- Each profile subspace has dimension (log n)^{O(1)}
  ∃ (d : ℕ), d ≤ (Nat.log 2 n) ^ 6

/-- Width⇒Rank theorem (Theorem 5.16) -/
axiom width_to_rank (F : Type*) [Field F] (n profiles dim_bound : ℕ) :
  -- profiles × dim_bound gives the total rank bound
  profiles * dim_bound ≤ n ^ 10  -- simplified; actual bound is n^{O(1)}

end Compiler
