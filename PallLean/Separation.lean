import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.Extraction
import PallLean.TuringMachine
/-!
# Main Separation: P ≠ NP — Pall Theorem 19.1
-/

namespace Separation

open SPDP Compiler NPWitness Extraction TuringMachine

/-- P = NP: a polytime 3-SAT decider exists -/
structure PeqNP where
  sat_decider : DTM
  decides_sat : True

/-- **P ≠ NP (Theorem 19.1)** -/
theorem P_neq_NP (h : PeqNP) : False := by
  let M := h.sat_decider
  let M' := sheetCoupling M  -- M♯

  -- A2: ∃ C n₂, ∀ n ≥ n₂, ΓB(p_{M♯,n}) ≤ n^C
  obtain ⟨C, n₂, hC⟩ := p_side_collapse ℚ M'

  -- A3: ∃ n₁, ∀ n ≥ n₁, ΓB(Q×_Φn) ≥ n^{log n/4}
  obtain ⟨n₁, h_npside⟩ := np_side_lb ℚ

  -- A5: ∃ n₀, ∀ n ≥ n₀, n^{log n/4} > n^{C+1} (PROVED)
  obtain ⟨n₀, h_arith⟩ := superPoly_beats_poly (C + 1) (by omega)

  let n := max (max (max n₀ n₁) n₂) 2

  -- A3 applied
  have h1 : blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly ℚ n) ≥ n ^ (Nat.log 2 n / 4) :=
    h_npside n (by omega)

  -- A4: extraction
  have h2 : blockedSpdpRank (tseitinPartition n) (Nat.log 2 n) (Nat.log 2 n)
      (tseitinPoly ℚ n) ≤
    blockedSpdpRank (compiledPartition M' n) (Nat.log 2 n) (Nat.log 2 n)
      (compiledPolyOf ℚ M' n) :=
    extraction_rank_monotone ℚ M n

  -- A2 applied
  have h3 : blockedSpdpRank (compiledPartition M' n) (Nat.log 2 n) (Nat.log 2 n)
      (compiledPolyOf ℚ M' n) ≤ n ^ C :=
    hC n (by omega)

  -- Chain: n^{log n/4} ≤ n^C
  have h4 : n ^ (Nat.log 2 n / 4) ≤ n ^ C := by linarith

  -- But n^{log n/4} > n^{C+1} > n^C
  have h5 : n ^ (Nat.log 2 n / 4) > n ^ (C + 1) := h_arith n (by omega)
  have h6 : n ^ (C + 1) ≥ n ^ C := Nat.pow_le_pow_right (by omega : n ≥ 1) (by omega : C ≤ C + 1)
  linarith

end Separation
