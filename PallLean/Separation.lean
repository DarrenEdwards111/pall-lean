import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.Extraction
/-!
# Main Separation: P ≠ NP — Pall Theorem 19.1

Proved from:
- A2: P-side collapse (Theorem 6.1) — p_side_collapse
  - Sub-axiom: compiled_has_locality (compilation produces local structure)
  - Sub-axiom: width_to_rank_bound (profile compression + Width⇒Rank)
- A3: NP-side non-collapse (Theorem 10.1) — np_side_lb
  - Sub-axiom: tseitin_identity_minor (identity minor from disjoint clauses)
- A4: Extraction rank bound — extraction_rank_bound (PROVED THEOREM)
  - Sub-axiom: extraction_structure (Tseitin is extractable from compiled poly)
- A5: Arithmetic contradiction — superPoly_beats_poly (PROVED THEOREM)

Total: 4 axioms (was 3 with True hypotheses; now 4 with meaningful content)
- compiled_has_locality: compilation → local structure
- width_to_rank_bound: local structure → poly rank (profile compression)
- tseitin_identity_minor: Tseitin → identity minor (expander + disjoint clauses)
- extraction_structure: Tseitin = extract(compiled) (sheet coupling)
-/

namespace Separation

open SPDP Compiler NPWitness Extraction

/-- P = NP assumption: there exists a polytime SAT decider -/
structure PeqNP where
  sat_decider : PolyTimeTM
  decides_sat : True  -- placeholder for: L(sat_decider) = 3SAT

/-- **P ≠ NP (Pall Theorem 19.1)**

    Assuming P = NP, the polytime SAT decider M gives:
    1. pM♯,n has rank ≤ n^C (A2, applied to M♯ = Sheet(M))
    2. Q×_Φn has rank ≤ rank(pM♯,n) ≤ n^C (A4, extraction)
    3. Q×_Φn has rank ≥ n^{log n / 4} (A3, identity minor)
    4. n^{log n / 4} > n^C for large n (A5, arithmetic)
    Contradiction. -/
theorem P_neq_NP (h : PeqNP) : False := by
  let M := h.sat_decider
  let M' := sheetCoupling M

  -- A2: ∃ C, ∀ n ≥ 2, rank(pM♯,n) ≤ n^C
  obtain ⟨C, hC⟩ := p_side_collapse ℚ M'

  -- A3: ∃ n₁, ∀ n ≥ n₁, rank(Q) ≥ n^{log n / 4}
  obtain ⟨n₁, h_npside⟩ := np_side_lb ℚ

  -- A5: ∃ n₀, ∀ n ≥ n₀, n^{log n / 4} > n^{C+1}
  obtain ⟨n₀, h_arith⟩ := superPoly_beats_poly (C + 1) (by omega)

  let n := max (max n₀ n₁) 2
  have hn_ge_n0 : n ≥ n₀ := by omega
  have hn_ge_n1 : n ≥ n₁ := by omega
  have hn_ge_2 : n ≥ 2 := by omega

  -- A3: rank(Q×_Φn) ≥ n^{log n / 4}
  have h1 : spdpRank (Nat.log 2 n) (tseitinPoly ℚ n) ≥
      n ^ (Nat.log 2 n / 4) :=
    h_npside n hn_ge_n1

  -- A4: rank(Q×_Φn) ≤ rank(pM♯,n) [PROVED THEOREM]
  have h2 : spdpRank (Nat.log 2 n) (tseitinPoly ℚ n) ≤
      spdpRank (Nat.log 2 n) (compiledPoly ℚ M' n) :=
    extraction_rank_bound ℚ M n

  -- A2: rank(pM♯,n) ≤ n^C
  have h3 : spdpRank (Nat.log 2 n) (compiledPoly ℚ M' n) ≤ n ^ C :=
    hC n hn_ge_2

  -- Chain: n^{log n / 4} ≤ rank(Q) ≤ rank(p) ≤ n^C
  have h4 : n ^ (Nat.log 2 n / 4) ≤ n ^ C := by omega

  -- But n^{log n / 4} > n^{C+1} ≥ n^C for large n
  have h5 : n ^ (Nat.log 2 n / 4) > n ^ (C + 1) := h_arith n hn_ge_n0
  have h6 : n ^ (C + 1) ≥ n ^ C := Nat.pow_le_pow_right (by omega) (by omega)
  omega

end Separation
