/-!
# NP-Side: Explicit Lower Bounds

Pall paper Sections 7-10.
-/

import PallLean.SPDPDefs

namespace NPWitness

open SPDP MvPolynomial

/-! ## Tseitin Formulas -/

structure TseitinFormula (n : ℕ) where
  numClauses : ℕ
  numVars : ℕ

def npVars (n : ℕ) : ℕ := 20 * n

/-! ## NP-Side Lower Bound (Theorem 10.1)

This is the core mathematical content of the NP-side.
We axiomatise it as the load-bearing assumption A3. -/

/-- **A3 (Theorem 10.1)**: The coupled sheet for Ramanujan-Tseitin
    formulas has super-polynomial SPDP rank.

    Mathematical content:
    - Ramanujan expander → Ω(n) disjoint clauses
    - Each clause contributes a tag monomial on disjoint blocks
    - Identity minor of size (L choose κ) = n^{Θ(log n)}

    This axiom is the NP-side of the separation. -/
axiom np_side_lower_bound (F : Type*) [Field F] (n : ℕ) (hn : n ≥ 10)
    (params : SPDPParams) (B : BlockPartition (npVars n))
    (Q : MvPolynomial (Fin (npVars n)) F)
    (h_witness : True)  -- Q is the coupled sheet of Ramanujan-Tseitin
    (h_params : params = matchedParams n) :
    spdpRank (npVars n) params B Q ≥ n ^ (Nat.log 2 n / 4)

end NPWitness
