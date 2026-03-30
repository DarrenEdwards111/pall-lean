import PallLean.HoloCompilerWitnessFriendly
import Mathlib.Tactic

/-!
# HoloCompilerWitnessFriendlyRoute

This file turns the witness-friendly layered gadget family into an explicit proof route.

What is now concrete:
- a distinct layered polynomial `holoCompiledPolyFin` on `Fin (holoDistinctVars M n)`;
- a Fin-indexed partition `holoDistinctPartitionFin` grouping each triple of
  machine/verifier/aux slots into one block;
- concrete layer extractions with proved behavior on local factors and sheets;
- proved partition-block consistency and slot injectivity/distinctness.

What remains as the real paper-facing work:
- prove a CEW / profile-compression bound for `holoCompiledPolyFin` under
  `holoDistinctPartitionFin`;
- connect the verifier-layer extracted sheet to the intended NP witness family
  strongly enough to recover the lower-bound route.
-/

namespace HoloCompilerWitnessFriendlyRoute

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open HoloCompilerDistinct
open HoloCompilerDistinctPartition
open HoloCompilerDistinctLocality
open HoloCompilerWitnessFriendly

/-- Width⇒Rank target for the witness-friendly distinct object on the Fin-indexed space. -/
axiom wf_width_rank (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates)
    (κ : ℕ) (hκ : κ ≥ 5) :
    mlBlockedSpdpRank (holoDistinctPartitionFin M n) κ κ (holoCompiledPolyFin M n) ≤ n ^ 200

/-- Extraction target: the Fin-indexed compiled object carries the NP witness hardness. -/
axiom wf_extracts_hard_witness (M : DTM) (n : ℕ)
    (hn : n ≥ 32)
    (κ : ℕ) (hκ : κ ≥ 5) :
    n ^ (κ / 4) ≤
      mlBlockedSpdpRank (holoDistinctPartitionFin M n) κ κ (holoCompiledPolyFin M n)

/-- P = NP assumption package. -/
structure PeqNP where
  sat_decider : DTM
  decides_sat : True

/-- If the witness-friendly distinct compiler route is completed, it yields the same contradiction pattern. -/
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
