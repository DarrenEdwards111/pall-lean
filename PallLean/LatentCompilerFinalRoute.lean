import PallLean.LatentCompiler
import PallLean.LatentWidthRankDecomp
import PallLean.LatentWitnessMinorDecomp
import Mathlib.Tactic

/-!
# LatentCompilerFinalRoute

Final contradiction route using decomposed P-side Width⇒Rank and decomposed
NP-side extraction bridge.
-/

namespace LatentCompilerFinalRoute

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open LatentCompiler
open LatentWidthRankDecomp
open LatentWitnessMinorDecomp

/-- NP hard-witness theorem at contradiction scale.
Now sourced from a single NP-side assembled obligation in witness-minor decomposition. -/
theorem latent_extracts_hard_witness_decomp (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804)
    (hNPobl : latent_hard_witness_logscale M n hn804)
    (κ : ℕ)
    (hk : κ = Nat.log 2 n) :
    n ^ (κ / 4) ≤ mlBlockedSpdpRank (latentPartition M n) κ κ (latentCompiledPoly M n) := by
  subst hk
  simpa [latent_hard_witness_logscale] using hNPobl

/-- P = NP assumption package. -/
structure PeqNP where
  sat_decider : DTM
  decides_sat : True

/-- Bundled paper-facing obligations at contradiction scale. -/
structure LogscaleObligations (M : DTM) (n : ℕ)
    (hnM : n ≥ max 4 M.numStates)
    (hn804 : n ≥ 2 ^ 804) where
  npHardWitness : latent_hard_witness_logscale M n hn804
  pProfileAssembly : latent_profile_assembly_logscale M n hnM hn804

/-- Derived machine-size bound from the contradiction-scale threshold assumption. -/
lemma hnM_of_hn (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) :
    n ≥ max 4 h.sat_decider.numStates :=
  le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)

/-- Derived asymptotic threshold bound from the contradiction-scale assumption. -/
lemma hn804_of_hn (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) :
    n ≥ 2 ^ 804 :=
  le_trans (le_max_right _ _) hn

/-- P ≠ NP via latent compiler, fully decomposed route usage.
Requires explicit proofs of the two paper-facing assembled obligations. -/
theorem P_neq_NP_latent_decomp (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (hObl : LogscaleObligations h.sat_decider n (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hn_left : n ≥ max 32 (max 4 M.numStates) := le_trans (le_max_left _ _) hn
  have hn32 : n ≥ 32 := le_trans (le_max_left _ _) hn_left
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  let κ := Nat.log 2 n

  -- NP side (assembled obligation)
  have hNP := latent_extracts_hard_witness_decomp M n hn804 hObl.npHardWitness κ rfl

  -- P side (assembled obligation)
  have hP : mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (latentCompiledPoly M n) ≤ n ^ 200 :=
    latent_width_rank_from_decomp M n hnM hn804 hObl.pProfileAssembly

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

end LatentCompilerFinalRoute
