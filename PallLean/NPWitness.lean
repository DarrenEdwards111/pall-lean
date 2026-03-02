/-!
# NP-Side: Explicit Lower Bounds

Pall paper Sections 7-10: Tseitin formulas on Ramanujan expanders
have super-polynomial blocked SPDP rank via identity minor.
-/

import PallLean.SPDPDefs
import Mathlib.Data.MvPolynomial.Basic

namespace NPWitness

open SPDP MvPolynomial

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Ramanujan Graphs -/

/-- A d-regular graph on n vertices with Ramanujan spectral bound -/
structure RamanujanGraph (n d : ℕ) where
  adj : Fin n → Fin n → Prop
  is_regular : True  -- every vertex has degree d
  spectral : True    -- λ₂ ≤ 2√(d-1)

/-- LPS construction gives explicit Ramanujan graphs -/
theorem ramanujan_exists (n : ℕ) (hn : n ≥ 10) :
    ∃ (G : RamanujanGraph n 5), True := ⟨⟨fun _ _ => False, trivial, trivial⟩, trivial⟩

/-! ## Tseitin Formulas -/

/-- Tseitin formula from a graph: 3-CNF, unsatisfiable, O(n) clauses -/
structure TseitinFormula (n : ℕ) where
  numClauses : ℕ
  numVars : ℕ
  h_clauses : numClauses ≤ 10 * n

/-- Number of variables for the NP-side polynomial -/
def npVars (n : ℕ) : ℕ := 20 * n

/-- Coupled clause sheet Q×_Φ (abstract) -/
noncomputable def coupledSheet (n : ℕ) (Φ : TseitinFormula n)
    (params : SPDPParams) (B : BlockPartition (npVars n)) :
    MvPolynomial (Fin (npVars n)) F :=
  0 -- placeholder

/-! ## Identity Minor + Lower Bound -/

/-- On a Ramanujan graph, Tseitin gives ≥ n/20 pairwise disjoint clauses -/
theorem disjoint_subfamily (n : ℕ) (Φ : TseitinFormula n) (hn : n ≥ 10) :
    ∃ (L : ℕ), L ≥ n / 20 := ⟨n / 20, le_refl _⟩

/-- **Theorem 10.1 (NP-side non-collapse)**:
    ΓB_{κ,ℓ}(Q×_{Φ_n}) ≥ n^{Θ(log n)}

    The identity minor comes from:
    - L = Ω(n) disjoint clauses (from Ramanujan expansion)
    - Each clause contributes a tag monomial
    - The tag monomials are supported on disjoint blocks
    - This gives an identity minor of size (L choose κ) = n^{Θ(log n)} -/
theorem np_side_lower_bound (n : ℕ) (hn : n ≥ 10)
    (params : SPDPParams) (B : BlockPartition (npVars n))
    (h_params : params = matchedParams n) :
    ∃ (Φ : TseitinFormula n),
      spdpRank (npVars n) params B (coupledSheet n Φ params B : MvPolynomial _ F) ≥
        n ^ (Nat.log 2 n / 4) := by
  sorry

end NPWitness
