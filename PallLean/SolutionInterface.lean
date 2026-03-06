import Mathlib

namespace PallSolutionInterface

/-
  This file isolates the actual remaining mathematical content.

  Already verified (0 axioms, 0 sorry's):
  • NP-side lower bound: Tseitin verifier has superpolynomial SPDP rank
  • P-side collapse: compiled Y*V polynomial has polynomial SPDP rank
  • Superpolynomial beats polynomial

  What remains is the bridge (extraction_rank_transfer):
  If a polynomial-time SAT solver M exists, then its compiled polynomial
  must realize a rank-preserving hardness transfer from the Tseitin instance.
-/

/-- Abstract proof schema: three pieces close the contradiction. -/
theorem contradiction_schema
    (npRank compiledRank : ℕ → ℕ)  -- rank as function of n
    (h_np : ∀ C, ∃ n₀, ∀ n ≥ n₀, npRank n > n ^ C)        -- NP: superpolynomial
    (h_transfer : ∀ n, npRank n ≤ compiledRank n)             -- extraction
    (h_p : ∃ C, ∀ n, compiledRank n ≤ n ^ C)                  -- P: polynomial
    : False := by
  obtain ⟨C, hC⟩ := h_p
  obtain ⟨n₀, hn₀⟩ := h_np C
  have h1 := hn₀ n₀ (le_refl _)
  have h2 := h_transfer n₀
  have h3 := hC n₀
  linarith

/-
  In the concrete pall-lean project:
  • h_np  is `np_side_lb`            — PROVED
  • h_p   is `p_side_collapse`       — PROVED
  • h_transfer is `extraction_rank_monotone` — OPEN (1 axiom)

  The extraction axiom is the decisive mathematical content:
  it asserts that a polynomial-time SAT solver's compiled polynomial
  inherits the algebraic hardness of the Tseitin formula.

  The tension discovered during formalization:
  • NP-side needs tseitin in PRODUCT form ∏(1 - z_c · G_c) for identity minor
  • P-side needs Y * V form (sum of local constraint squares) for collapse
  • These structures are incompatible in a single polynomial

  This is not a formalization gap — it IS the mathematical content of P ≠ NP.
-/

end PallSolutionInterface
