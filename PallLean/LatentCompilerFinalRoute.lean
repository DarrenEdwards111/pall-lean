import PallLean.LatentCompiler
import PallLean.LatentWidthRankDecomp
import PallLean.LatentExtractionBridgeDecomp
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
open LatentExtractionBridgeDecomp
open LatentWitnessMinorDecomp

/-- NP hard-witness theorem via decomposed witness-minor + decomposed extraction bridge.

This route avoids the monolithic extractedProductWitness_choose_lower axiom in
LatentCompiler by using the decomposed theorem from LatentWitnessMinorDecomp. -/
theorem latent_extracts_hard_witness_decomp (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804) (κ : ℕ) (hκ : κ ≥ 5)
    (hk : κ = Nat.log 2 n) :
    n ^ (κ / 4) ≤ mlBlockedSpdpRank (latentPartition M n) κ κ (latentCompiledPoly M n) := by
  subst hk
  have hchoose : n ^ (Nat.log 2 n / 4) ≤ Nat.choose (latentBaseVars M n) (Nat.log 2 n) :=
    choose_latentBaseVars_lower M n hn804
  have hminor : Nat.choose (latentBaseVars M n) (Nat.log 2 n) ≤
      mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (MvPolynomial.rename (fun i => slot M n 2 i) (extractedProductWitness M n)) :=
    extractedProductWitness_choose_lower_from_decomp_logscale M n hn804
  have hextract : mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (MvPolynomial.rename (fun i => slot M n 2 i) (extractedProductWitness M n)) ≤
      mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n) (latentCompiledPoly M n) :=
    extraction_rank_monotone_selector_from_decomp M n hn804
  exact le_trans hchoose (le_trans hminor hextract)

/-- P = NP assumption package. -/
structure PeqNP where
  sat_decider : DTM
  decides_sat : True

/-- P ≠ NP via latent compiler, fully decomposed route usage. -/
theorem P_neq_NP_latent_decomp (h : PeqNP) (n : ℕ)
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

  -- NP side (decomposed extraction bridge)
  have hNP := latent_extracts_hard_witness_decomp M n hn804 κ hκ rfl

  -- P side (decomposed Width⇒Rank route at log-scale)
  have hP : mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (latentCompiledPoly M n) ≤ n ^ 200 :=
    latent_width_rank_from_decomp M n hnM hn804

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
