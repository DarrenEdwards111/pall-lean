import PallLean.MultilinearSPDP
import PallLean.NPWitness
import PallLean.Compiler
import PallLean.GodMoveCompilerRoute
import Mathlib.Tactic

namespace PneqNP

open SPDP MultilinearSPDP TuringMachine Compiler NPWitness Tseitin
open GodMoveCompilerRoute

structure PeqNP where
  sat_decider : DTM
  decides_sat : True

theorem P_neq_NP (h : PeqNP) : False := by
  let M := h.sat_decider
  obtain ⟨C, hpside⟩ := pside_full_ml_rank_bound M
  obtain ⟨n₁, hnpside⟩ := np_ml_lower_bound ℚ
  obtain ⟨n₀, harith⟩ := SPDP.superPoly_beats_poly (C + 1) (by omega)
  let n := 2 * max (max (max n₀ n₁) (max 32 M.numStates)) 32
  have heven : 2 ∣ n := ⟨_, rfl⟩
  have hn32 : n ≥ 32 := by
    dsimp [n]
    omega
  have h_le : npNumVars n ≤ numVars M n (Nat.log 2 n) := by
    have hv : (tseitinAt n).graph.numVertices = n :=
      tseitinAt_vertices n (by omega) heven
    have hedges : (tseitinAt n).graph.numEdges ≤ 10 * n := by
      calc
        (tseitinAt n).graph.numEdges ≤ (tseitinAt n).graph.numVertices * (tseitinAt n).graph.degree :=
          (tseitinAt n).graph.edges_bound
        _ ≤ n * 10 := by
          rw [hv]
          gcongr
          exact (tseitinAt n).graph.degree_bound
        _ = 10 * n := by linarith
    have hclauses : (tseitinAt n).clauses.length ≤ 10 * n := by
      calc
        (tseitinAt n).clauses.length ≤ 10 * (tseitinAt n).graph.numVertices :=
          (tseitinAt n).num_clauses_upper
        _ = 10 * n := by rw [hv]
    have hnp : npNumVars n ≤ 50 * n := by
      have he := hedges
      have hc := hclauses
      unfold npNumVars tseitinNumVars at *
      linarith
    have hpow : n ≤ timeSteps M n := by
      unfold timeSteps
      simpa using (Nat.pow_le_pow_right (show n ≥ 1 by omega) M.hTimeBound)
    have hS : n + 1 ≤ tapeSize M n := by
      unfold tapeSize
      omega
    have hbig : 50 * n ≤ tapeSize M n * tapeSize M n + tapeSize M n * tapeSize M n := by
      calc
        50 * n ≤ 2 * (n + 1) * (n + 1) := by nlinarith
        _ ≤ 2 * tapeSize M n * tapeSize M n := by
          gcongr
        _ = tapeSize M n * tapeSize M n + tapeSize M n * tapeSize M n := by ring
    calc
      npNumVars n ≤ 50 * n := hnp
      _ ≤ numVars M n (Nat.log 2 n) := by
        unfold numVars
        have hS2 := hS
        nlinarith [hbig]
  have h_np := hnpside n (by omega) heven
  have hκ_ge : Nat.log 2 n ≥ 5 := by
    have : Nat.log 2 32 = 5 := by native_decide
    exact le_trans (by omega) (Nat.log_mono_right hn32)
  have h_extract := godMove_extraction_rank_monotone ℚ M n h.decides_sat (by omega)
    h_le (Nat.log 2 n) (Nat.log 2 n) hκ_ge
  have h_pside := hpside n (by show n ≥ max 4 M.numStates; omega) h_le
    (Nat.log 2 n) hκ_ge (Nat.le_refl _)
  have h_chain : n ^ (Nat.log 2 n / 4) ≤ n ^ C := by linarith
  have h_contra := harith n (by omega)
  linarith [Nat.pow_le_pow_right (show n ≥ 1 by omega) (show C ≤ C + 1 by omega)]

end PneqNP
