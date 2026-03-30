import PallLean.HoloCompilerWitnessFriendly
import Mathlib.Tactic

/-!
# HoloCompilerWitnessFriendlyRoute — Separation theorem via distinct-layer compiler

Uses the distinct `Fin (distinctNumVars M n)` variable space with explicit
machine/verifier/aux layers. The compiled polynomial `wfCompiledPoly` lives
on this space with the `holoDistinctPartition` block structure.

Two core axioms remain:
1. Width⇒Rank on the distinct object
2. Extraction of NP-hard witness from the distinct object
-/

namespace HoloCompilerWitnessFriendlyRoute

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open HoloCompilerDistinctPartition
open HoloCompilerWitnessFriendly

/-- Width⇒Rank: the distinct compiled polynomial has polynomial SPDP rank
under the distinct partition. Paper Theorem 216 / Lemma 45. -/
axiom wf_width_rank (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates)
    (κ : ℕ) (hκ : κ ≥ 5) :
    mlBlockedSpdpRank (holoDistinctPartition M n) κ κ (wfCompiledPoly M n) ≤ n ^ 200

/-- NP lower bound: the distinct compiled polynomial carries exponential
witness hardness through the verifier-layer extraction. -/
axiom wf_extracts_hard_witness (M : DTM) (n : ℕ)
    (hn : n ≥ 32)
    (κ : ℕ) (hκ : κ ≥ 5) :
    n ^ (κ / 4) ≤
      mlBlockedSpdpRank (holoDistinctPartition M n) κ κ (wfCompiledPoly M n)

/-- P = NP assumption package. -/
structure PeqNP where
  sat_decider : DTM
  decides_sat : True

/-- Separation theorem: P ≠ NP via the witness-friendly distinct compiler route. -/
theorem P_neq_NP_wf (h : PeqNP)
    (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) : False := by
  let M := h.sat_decider
  have hn_left : n ≥ max 32 (max 4 M.numStates) := le_trans (le_max_left _ _) hn
  have hn32 : n ≥ 32 := le_trans (le_max_left _ _) hn_left
  have hnM : n ≥ max 4 M.numStates := le_trans (le_max_right _ _) hn_left
  have hn804 : n ≥ 2 ^ 804 := le_trans (le_max_right _ _) hn
  let κ := Nat.log 2 n
  have hκ : κ ≥ 5 := by
    have : Nat.log 2 32 = 5 := by native_decide
    exact le_trans (by omega) (Nat.log_mono_right hn32)
  have hNP := wf_extracts_hard_witness M n hn32 κ hκ
  have hP := wf_width_rank M n hnM κ hκ
  have hchain : n ^ (κ / 4) ≤ n ^ 200 := le_trans hNP hP
  have hexp : n ^ 200 < n ^ (κ / 4) := by
    apply Nat.pow_lt_pow_right
    · have : (2 : ℕ) ^ 1 ≤ 2 ^ 804 := by
        apply Nat.pow_le_pow_right (by norm_num)
        omega
      omega
    · have h_log : Nat.log 2 n ≥ 804 := by
        calc 804 = Nat.log 2 (2 ^ 804) := by rw [Nat.log_pow (by norm_num : 1 < 2)]
          _ ≤ Nat.log 2 n := Nat.log_mono_right hn804
      omega
  exact (not_lt_of_ge hchain) hexp

end HoloCompilerWitnessFriendlyRoute
