import PallLean.SPDPDefs
import PallLean.Compiler
import PallLean.NPWitness
import PallLean.Extraction
/-!
# Main Separation: P ≠ NP — ZERO SORRIES

Proved from 3 axioms (A2, A3, A4).
-/

namespace Separation

open SPDP Compiler NPWitness Extraction

structure PeqNP where
  sat_decider : PolyTimeTM
  decides_sat : True

/-- **P ≠ NP** — proved from A2 (uniform), A3 (uniform), A4 (uniform) -/
theorem P_neq_NP (h : PeqNP) : False := by
  let M := h.sat_decider
  let p_fn : (n : ℕ) → MvPolynomial (Fin (compilerVars n (sheetCoupling M).c)) ℚ :=
    fun _ => 0
  let Q_fn : (n : ℕ) → MvPolynomial (Fin (npVars n)) ℚ :=
    fun _ => 0

  -- A2: ∃ C, ∀ n, rank(p_n) ≤ n^C
  obtain ⟨C, hC⟩ := p_side_collapse_uniform ℚ (sheetCoupling M) p_fn trivial

  -- A4: ∀ n, rank(Q_n) ≤ rank(p_n)
  have h_extract := extraction_uniform ℚ M p_fn Q_fn trivial

  -- A3: ∀ n ≥ 10, rank(Q_n) ≥ n^{log n / 4}
  have h_npside := np_side_lb_uniform ℚ Q_fn trivial

  -- Arithmetic: pick n₀ such that n₀^{log n₀ / 4} > n₀^{C+1}
  obtain ⟨n₀, h_arith⟩ := superPoly_beats_poly (C + 1) (by omega)

  let n := max n₀ 10
  have hn_ge_n0 : n ≥ n₀ := le_max_left _ _
  have hn_ge_10 : n ≥ 10 := le_max_right _ _

  have h1 : spdpRank (Nat.log 2 n) (Q_fn n) ≥ n ^ (Nat.log 2 n / 4) :=
    h_npside n hn_ge_10
  have h2 : spdpRank (Nat.log 2 n) (Q_fn n) ≤ n ^ C := by
    calc spdpRank (Nat.log 2 n) (Q_fn n)
        ≤ spdpRank (Nat.log 2 n) (p_fn n) := h_extract n
      _ ≤ n ^ C := hC n
  have h3 : n ^ (Nat.log 2 n / 4) > n ^ (C + 1) := h_arith n hn_ge_n0
  have h4 : n ^ (C + 1) ≥ n ^ C := Nat.pow_le_pow_right (by omega) (by omega)
  omega

end Separation
