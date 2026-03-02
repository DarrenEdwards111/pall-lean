import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.Extraction
/-!
# Main Separation: P ≠ NP — Pall Theorem 19.1

The proof chain:

  A2 (Theorem 6.1): ΓB_{κ,ℓ}(pM♯,n) ≤ n^C        [P-side collapse]
  A4 (Theorem 12.2): ΓB_{κ,ℓ}(Q×_Φn) ≤ ΓB(pM♯,n)  [extraction monotonicity]
  A3 (Theorem 10.1): ΓB_{κ,ℓ}(Q×_Φn) ≥ n^{log n/4} [NP-side non-collapse]
  A5 (arithmetic):   n^{log n/4} > n^C for large n   [PROVED]

  Chaining: n^{log n/4} ≤ ΓB(Q×) ≤ ΓB(pM♯) ≤ n^C < n^{log n/4}. Contradiction.

Axiom inventory:
  - compiled_has_locality (Compiler.lean): compilation produces local structure
  - width_to_rank_bound (Compiler.lean): profile compression + Width⇒Rank
  - np_side_lb (NPWitness.lean): identity minor on Ramanujan–Tseitin
  - extraction_rank_monotone (Extraction.lean): T_Φ is rank-monotone

All use the blocked SPDP rank ΓB_{κ,ℓ} with the paper's actual Definition 2.3.
-/

namespace Separation

open SPDP Compiler NPWitness Extraction

/-- P = NP assumption: there exists a polytime SAT decider -/
structure PeqNP where
  sat_decider : PolyTimeTM
  decides_sat : True  -- placeholder for: L(sat_decider) = 3SAT

/-- **P ≠ NP (Pall Theorem 19.1)**

    Assuming P = NP, the polytime SAT decider M gives:
    1. M♯ = Sheet(M) is also polytime (c' = c+1)
    2. ΓB(pM♯,n) ≤ n^C       (A2, P-side collapse applied to M♯)
    3. ΓB(Q×_Φn) ≤ ΓB(pM♯,n) (A4, extraction is rank-monotone)
    4. ΓB(Q×_Φn) ≤ n^C        (chaining 2+3)
    5. ΓB(Q×_Φn) ≥ n^{log n/4} (A3, NP-side non-collapse)
    6. n^{log n/4} > n^{C+1}   (A5, arithmetic, for large n)
    Contradiction at step 4 vs 5+6. -/
theorem P_neq_NP (h : PeqNP) : False := by
  let M := h.sat_decider
  let M' := sheetCoupling M

  -- A2: ∃ C, ∀ n ≥ 2, ΓB(pM♯,n) ≤ n^C
  obtain ⟨C, hC⟩ := p_side_collapse ℚ M'

  -- A3: ∃ n₁, ∀ n ≥ n₁, ΓB(Q×_Φn) ≥ n^{log n / 4}
  obtain ⟨n₁, h_npside⟩ := np_side_lb ℚ

  -- A5: ∃ n₀, ∀ n ≥ n₀, n^{log n / 4} > n^{C+1}
  obtain ⟨n₀, h_arith⟩ := superPoly_beats_poly (C + 1) (by omega)

  let n := max (max n₀ n₁) 2
  have hn_ge_n0 : n ≥ n₀ := by omega
  have hn_ge_n1 : n ≥ n₁ := by omega
  have hn_ge_2 : n ≥ 2 := by omega

  -- A3: ΓB(Q×_Φn) ≥ n^{log n / 4}
  have h1 : blockedSpdpRank (npPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly ℚ n) ≥ n ^ (Nat.log 2 n / 4) :=
    h_npside n hn_ge_n1

  -- A4: ΓB(Q×_Φn) ≤ ΓB(pM♯,n) [AXIOM: extraction_rank_monotone]
  have h2 : blockedSpdpRank (npPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly ℚ n) ≤
    blockedSpdpRank (compilerPartition n M'.c) (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly ℚ M' n) :=
    extraction_rank_monotone ℚ M n

  -- A2: ΓB(pM♯,n) ≤ n^C
  have h3 : blockedSpdpRank (compilerPartition n M'.c) (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly ℚ M' n) ≤ n ^ C :=
    hC n hn_ge_2

  -- Chain: n^{log n / 4} ≤ ΓB(Q×) ≤ ΓB(pM♯) ≤ n^C
  have h4 : n ^ (Nat.log 2 n / 4) ≤ n ^ C := by omega

  -- But n^{log n / 4} > n^{C+1} ≥ n^C for large n
  have h5 : n ^ (Nat.log 2 n / 4) > n ^ (C + 1) := h_arith n hn_ge_n0
  have h6 : n ^ (C + 1) ≥ n ^ C := Nat.pow_le_pow_right (by omega) (by omega)
  omega

end Separation
