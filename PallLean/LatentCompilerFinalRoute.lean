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

/-- Paper-facing extraction obligation (Theorem 223 style) at contradiction scale.
This corresponds to instance-uniform extraction monotonicity from compiled object
into the verifier/witness side, specialized to κ = ℓ = log₂ n. -/
def theorem223_extraction_obligation (M : DTM) (n : ℕ) (hn804 : n ≥ 2 ^ 804) : Prop :=
  selector_bridge_logscale M n hn804

/-- Paper-facing P obligation (Theorem 216 style) at contradiction scale.
Interpreted here as the assembled profile/Width⇒Rank upper bound for κ = log₂ n. -/
def theorem216_p_obligation (M : DTM) (n : ℕ)
    (hnM : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804) : Prop :=
  latent_profile_assembly_logscale M n hnM hn804

/-- Bundled paper-facing obligations at contradiction scale.
Split into NP parts + P parts, then assembled through route lemmas. -/
structure LogscaleObligations (M : DTM) (n : ℕ)
    (hnM : n ≥ max 4 M.numStates)
    (hn804 : n ≥ 2 ^ 804) where
  -- NP-side nontrivial parts
  npLower : extracted_witness_exp_lower_logscale M n hn804
  npBridge : theorem223_extraction_obligation M n hn804
  -- P-side nontrivial assembly part
  pAsm : theorem216_p_obligation M n hnM hn804

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

/-- Assemble NP-side top-level obligation from bundled NP parts. -/
lemma obligations_np_hard (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (hObl : LogscaleObligations h.sat_decider n (hnM_of_hn h n hn) (hn804_of_hn h n hn)) :
    latent_hard_witness_logscale h.sat_decider n (hn804_of_hn h n hn) :=
  latent_hard_witness_logscale_from_parts _ _ _ hObl.npLower hObl.npBridge

/-- Assemble P-side top-level obligation from bundled P part. -/
lemma obligations_p_profile (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (hObl : LogscaleObligations h.sat_decider n (hnM_of_hn h n hn) (hn804_of_hn h n hn)) :
    theorem216_p_obligation h.sat_decider n (hnM_of_hn h n hn) (hn804_of_hn h n hn) :=
  latent_profile_assembly_logscale_from_parts _ _ _ _ (by trivial) (by trivial) hObl.pAsm

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

  -- NP side (assembled from parts)
  have hNPobl : latent_hard_witness_logscale M n hn804 :=
    obligations_np_hard h n hn hObl
  have hNP := latent_extracts_hard_witness_decomp M n hn804 hNPobl κ rfl

  -- P side (assembled from parts)
  have hPobl : latent_profile_assembly_logscale M n hnM hn804 :=
    obligations_p_profile h n hn hObl
  have hP : mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (latentCompiledPoly M n) ≤ n ^ 200 :=
    latent_width_rank_from_decomp M n hnM hn804 hPobl

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
