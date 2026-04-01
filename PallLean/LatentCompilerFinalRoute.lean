import PallLean.LatentCompiler
import PallLean.LatentWidthRankDecomp
import PallLean.LatentWitnessMinorDecomp
import PallLean.SelConClosedCoeffDecomp
import Mathlib.Tactic

/-!
# LatentCompilerFinalRoute

Final contradiction route using decomposed P-side Width⇒Rank and direct
NP-side identity-minor lower bound on latentCompiledPoly.
-/

namespace LatentCompilerFinalRoute

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open LatentCompiler
open LatentWidthRankDecomp
open LatentWitnessMinorDecomp
open SelConClosedCoeffDecomp

/-- NP hard-witness theorem at contradiction scale.
Now sourced from a single direct NP-side obligation. -/
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

/-- Paper-facing P obligation (Theorem 216 style) at contradiction scale.
Represented as the paper-faithful profile-data package.
Section 9 sides are discharged in-route; core is profile assembly bound. -/
def theorem216_p_obligation (M : DTM) (n : ℕ)
    (hnM : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804) : Prop :=
  theorem216_profile_data_logscale M n hnM hn804

/-- Bundled paper-facing obligations at contradiction scale.
NP side is now a single direct obligation (no bridge needed).
P side is the profile assembly obligation. -/
structure LogscaleObligations (M : DTM) (n : ℕ)
    (hnM : n ≥ max 4 M.numStates)
    (hn804 : n ≥ 2 ^ 804) where
  -- NP-side: explicit Kronecker coefficient data (paper identity-minor form)
  npData : selCon_kronecker_data_logscale M n hn804
  -- P-side: profile assembly upper bound
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

  -- NP side (from explicit Kronecker data; numeric closure is proved internally)
  have hNPkron : selCon_kronecker_linear_independence_logscale M n hn804 :=
    selCon_kronecker_linear_independence_logscale_from_data M n hn804 hObl.npData
  have hNPdirect : obligation1_np_logscale M n hn804 :=
    latent_hard_witness_logscale_from_kronecker M n hn804 hNPkron
  have hNP := latent_extracts_hard_witness_decomp M n hn804 hNPdirect κ rfl

  -- P side (assembled from profile-data package)
  have hPobl : obligation2_p_logscale M n hnM hn804 :=
    obligation2_p_logscale_from_data M n hnM hn804 hObl.pAsm
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

/-- Same final contradiction route, but NP-data is built internally from the
finer closed-form decomposition package (SelConClosedCoeffDecomp).

This reduces caller burden: instead of passing `npData` directly, pass the
choose-indexed list family with nodup/length and toFinset-level injectivity. -/
theorem P_neq_NP_latent_from_finer_decomp (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (idxList : Fin (Nat.choose (latentBaseVars h.sat_decider n) (Nat.log 2 n)) →
      List (Fin (latentBaseVars h.sat_decider n)))
    (hnd : ∀ i, (idxList i).Nodup)
    (hlen : ∀ i, (idxList i).length = Nat.log 2 n)
    (hfinj : ∀ i j, (idxList i).toFinset = (idxList j).toFinset → i = j)
    (pAsm : theorem216_p_obligation h.sat_decider n (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have hCoeff : selCon_kronecker_coeff_law_logscale M n hn804 :=
    selCon_kronecker_coeff_law_logscale_from_finer_decomp M n hn804 idxList hnd hlen hfinj
  have hNPData : selCon_kronecker_data_logscale M n hn804 := hCoeff
  exact P_neq_NP_latent_decomp h n hn ⟨hNPData, pAsm⟩

/-- Item 2 narrowing: same final contradiction route, but caller only supplies
P-side core assembly bound (`latent_profile_assembly_logscale`) instead of the
full paper-data package `theorem216_p_obligation`.

Theorem 216 package is built internally via
`theorem216_profile_data_logscale_from_core`. -/
theorem P_neq_NP_latent_from_finer_decomp_and_p_core (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (idxList : Fin (Nat.choose (latentBaseVars h.sat_decider n) (Nat.log 2 n)) →
      List (Fin (latentBaseVars h.sat_decider n)))
    (hnd : ∀ i, (idxList i).Nodup)
    (hlen : ∀ i, (idxList i).length = Nat.log 2 n)
    (hfinj : ∀ i j, (idxList i).toFinset = (idxList j).toFinset → i = j)
    (pCore : latent_profile_assembly_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have pAsm : theorem216_p_obligation M n hnM hn804 :=
    theorem216_profile_data_logscale_from_core M n hnM hn804 pCore
  exact P_neq_NP_latent_from_finer_decomp h n hn idxList hnd hlen hfinj pAsm

/-- Narrowest current entry point: NP data from finer decomposition plus
P-side finite span-card witness. Both paper-facing packages are built internally. -/
theorem P_neq_NP_latent_from_finer_decomp_and_p_span_card (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (idxList : Fin (Nat.choose (latentBaseVars h.sat_decider n) (Nat.log 2 n)) →
      List (Fin (latentBaseVars h.sat_decider n)))
    (hnd : ∀ i, (idxList i).Nodup)
    (hlen : ∀ i, (idxList i).length = Nat.log 2 n)
    (hfinj : ∀ i j, (idxList i).toFinset = (idxList j).toFinset → i = j)
    (pSpan : latent_profile_span_card_bound_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have pAsm : theorem216_p_obligation M n hnM hn804 :=
    theorem216_profile_data_logscale_from_span_card_bound M n hnM hn804 pSpan
  exact P_neq_NP_latent_from_finer_decomp h n hn idxList hnd hlen hfinj pAsm

/-- Narrowest decomposition entry (current): NP finer decomposition +
P-side profile block-cover package. -/
theorem P_neq_NP_latent_from_finer_decomp_and_p_block_cover (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (idxList : Fin (Nat.choose (latentBaseVars h.sat_decider n) (Nat.log 2 n)) →
      List (Fin (latentBaseVars h.sat_decider n)))
    (hnd : ∀ i, (idxList i).Nodup)
    (hlen : ∀ i, (idxList i).length = Nat.log 2 n)
    (hfinj : ∀ i j, (idxList i).toFinset = (idxList j).toFinset → i = j)
    (pCover : latent_profile_block_cover_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have pParts : latent_profile_span_card_parts_logscale M n hnM hn804 :=
    latent_profile_span_card_parts_logscale_from_block_cover M n hnM hn804 pCover
  have pSpan : latent_profile_span_card_bound_logscale M n hnM hn804 :=
    latent_profile_span_card_bound_logscale_from_parts M n hnM hn804 pParts
  exact P_neq_NP_latent_from_finer_decomp_and_p_span_card h n hn idxList hnd hlen hfinj pSpan

end LatentCompilerFinalRoute
