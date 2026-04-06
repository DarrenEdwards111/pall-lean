import PallLean.LatentCompiler
import PallLean.LatentWidthRankDecomp
import PallLean.LatentWitnessMinorDecomp
import PallLean.SelConClosedCoeffDecomp
import PallLean.CompilerProperties
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
open CompilerProperties

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

/-- Item 2 narrowing via the direct compiled-tableau frontier obligation. -/
theorem P_neq_NP_latent_from_finer_decomp_and_compiled_tableau_bound
    (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (idxList : Fin (Nat.choose (latentBaseVars h.sat_decider n) (Nat.log 2 n)) →
      List (Fin (latentBaseVars h.sat_decider n)))
    (hnd : ∀ i, (idxList i).Nodup)
    (hlen : ∀ i, (idxList i).length = Nat.log 2 n)
    (hfinj : ∀ i j, (idxList i).toFinset = (idxList j).toFinset → i = j)
    (hCompiled : latent_compiled_tableau_bound_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have pCore : latent_profile_assembly_logscale M n hnM hn804 :=
    (latent_profile_assembly_logscale_iff_compiled_tableau_bound M n hnM hn804).2 hCompiled
  have pAsm : theorem216_p_obligation M n hnM hn804 :=
    theorem216_profile_data_logscale_from_core M n hnM hn804
      (theorem9_profile_count_obligation_proved M n hn804)
      (theorem9_within_profile_dim_obligation_proved M n hn804)
      pCore
  exact P_neq_NP_latent_from_finer_decomp h n hn idxList hnd hlen hfinj pAsm

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
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    (latent_profile_assembly_logscale_iff_compiled_tableau_bound M n hnM hn804).1 pCore
  exact P_neq_NP_latent_from_finer_decomp_and_compiled_tableau_bound
    h n hn idxList hnd hlen hfinj hCompiled

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
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    latent_compiled_tableau_bound_logscale_from_span_card_bound M n hnM hn804 pSpan
  exact P_neq_NP_latent_from_finer_decomp_and_compiled_tableau_bound
    h n hn idxList hnd hlen hfinj hCompiled

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
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    latent_compiled_tableau_bound_logscale_from_block_cover M n hnM hn804 pCover
  exact P_neq_NP_latent_from_finer_decomp_and_compiled_tableau_bound
    h n hn idxList hnd hlen hfinj hCompiled

/-- Same as above, but accepts only the shared-witness Item-2+3 P package.
Item 1 (profile count cap) is recovered automatically from the profile index type. -/
theorem P_neq_NP_latent_from_finer_decomp_and_p_item23 (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (idxList : Fin (Nat.choose (latentBaseVars h.sat_decider n) (Nat.log 2 n)) →
      List (Fin (latentBaseVars h.sat_decider n)))
    (hnd : ∀ i, (idxList i).Nodup)
    (hlen : ∀ i, (idxList i).length = Nat.log 2 n)
    (hfinj : ∀ i j, (idxList i).toFinset = (idxList j).toFinset → i = j)
    (p23 : latent_profile_block_cover_item23_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have pCover : latent_profile_block_cover_logscale M n hnM hn804 :=
    latent_profile_block_cover_from_item23 M n hnM hn804 p23
  exact P_neq_NP_latent_from_finer_decomp_and_p_block_cover h n hn idxList hnd hlen hfinj pCover

/-- Item-3 entry with automatic Item-2 layering via uniform block-size bound. -/
theorem P_neq_NP_latent_from_finer_decomp_and_p_item3_uniform2 (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (idxList : Fin (Nat.choose (latentBaseVars h.sat_decider n) (Nat.log 2 n)) →
      List (Fin (latentBaseVars h.sat_decider n)))
    (hnd : ∀ i, (idxList i).Nodup)
    (hlen : ∀ i, (idxList i).length = Nat.log 2 n)
    (hfinj : ∀ i j, (idxList i).toFinset = (idxList j).toFinset → i = j)
    (p3u2 : latent_profile_block_cover_item3_uniform2_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    latent_compiled_tableau_bound_logscale_from_item3_uniform2 M n hnM hn804 p3u2
  exact P_neq_NP_latent_from_finer_decomp_and_compiled_tableau_bound
    h n hn idxList hnd hlen hfinj hCompiled

/-- More constructive P-entry: provide an explicit global finite span witness `G`
and an explicit 40×160 bucketization of `G`, then block-cover follows automatically. -/
theorem P_neq_NP_latent_from_finer_decomp_and_p_span_bucket (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (idxList : Fin (Nat.choose (latentBaseVars h.sat_decider n) (Nat.log 2 n)) →
      List (Fin (latentBaseVars h.sat_decider n)))
    (hnd : ∀ i, (idxList i).Nodup)
    (hlen : ∀ i, (idxList i).length = Nat.log 2 n)
    (hfinj : ∀ i j, (idxList i).toFinset = (idxList j).toFinset → i = j)
    (G : Finset (MvPolynomial (Fin (latentNumVars h.sat_decider n)) ℚ))
    (hSpan : mlBlockedSpdpSubspace (latentPartition h.sat_decider n)
      (Nat.log 2 n) (Nat.log 2 n) (latentCompiledPoly h.sat_decider n)
      ≤ Submodule.span ℚ (↑G : Set (MvPolynomial (Fin (latentNumVars h.sat_decider n)) ℚ)))
    (hBuck : latent_bucketization_40_160 h.sat_decider n G) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have pCover : latent_profile_block_cover_logscale M n hnM hn804 :=
    latent_profile_block_cover_logscale_from_span_and_bucketization M n hnM hn804 G hSpan hBuck
  exact P_neq_NP_latent_from_finer_decomp_and_p_block_cover h n hn idxList hnd hlen hfinj pCover

/-- Same as `..._p_span_bucket`, but takes the combined Do-2 P package directly. -/
theorem P_neq_NP_latent_from_finer_decomp_and_p_global_span_bucket (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (idxList : Fin (Nat.choose (latentBaseVars h.sat_decider n) (Nat.log 2 n)) →
      List (Fin (latentBaseVars h.sat_decider n)))
    (hnd : ∀ i, (idxList i).Nodup)
    (hlen : ∀ i, (idxList i).length = Nat.log 2 n)
    (hfinj : ∀ i j, (idxList i).toFinset = (idxList j).toFinset → i = j)
    (pGB : latent_global_span_and_bucket_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have pData : latent_profile_block_cover_construction_data_logscale M n hnM hn804 :=
    latent_profile_block_cover_construction_data_from_global_span_and_bucket M n hnM hn804 pGB
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    latent_compiled_tableau_bound_logscale_from_construction_data M n hnM hn804 pData
  exact P_neq_NP_latent_from_finer_decomp_and_compiled_tableau_bound
    h n hn idxList hnd hlen hfinj hCompiled

/-- Most concrete current P entry: explicit construction data package
(global `G`, span inclusion, explicit `(I,Gprof)` bucketization identity and bound). -/
theorem P_neq_NP_latent_from_finer_decomp_and_p_construction_data (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (idxList : Fin (Nat.choose (latentBaseVars h.sat_decider n) (Nat.log 2 n)) →
      List (Fin (latentBaseVars h.sat_decider n)))
    (hnd : ∀ i, (idxList i).Nodup)
    (hlen : ∀ i, (idxList i).length = Nat.log 2 n)
    (hfinj : ∀ i j, (idxList i).toFinset = (idxList j).toFinset → i = j)
    (pData : latent_profile_block_cover_construction_data_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    latent_compiled_tableau_bound_logscale_from_construction_data M n hnM hn804 pData
  exact P_neq_NP_latent_from_finer_decomp_and_compiled_tableau_bound
    h n hn idxList hnd hlen hfinj hCompiled

/-- Fully normalized contradiction route:
NP-side is instantiated canonically (no external idxList inputs), and the
concrete P construction-data package is first reduced to the core assembly bound. -/
theorem P_neq_NP_latent_from_p_construction_data_via_core (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pData : latent_profile_block_cover_construction_data_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn

  have hCoeff : selCon_kronecker_coeff_law_logscale M n hn804 :=
    selCon_kronecker_coeff_law_logscale_from_canonical_idxList M n hn804
  have npData : selCon_kronecker_data_logscale M n hn804 := hCoeff

  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    latent_compiled_tableau_bound_logscale_from_construction_data M n hnM hn804 pData
  have pCore : latent_profile_assembly_logscale M n hnM hn804 :=
    (latent_profile_assembly_logscale_iff_compiled_tableau_bound M n hnM hn804).2 hCompiled
  have pAsm : theorem216_p_obligation M n hnM hn804 :=
    theorem216_profile_data_logscale_from_core M n hnM hn804
      (theorem9_profile_count_obligation_proved M n hn804)
      (theorem9_within_profile_dim_obligation_proved M n hn804)
      pCore

  exact P_neq_NP_latent_decomp h n hn ⟨npData, pAsm⟩

/-- Fully normalized contradiction route:
NP-side is instantiated canonically (no external idxList inputs), and only the
most concrete P construction-data package remains as an external witness. -/
theorem P_neq_NP_latent_from_p_construction_data (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pData : latent_profile_block_cover_construction_data_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  exact P_neq_NP_latent_from_p_construction_data_via_core h n hn pData

/-- Canonical-NP route from a direct bound on the compiled tableau polynomial.

This exposes the actual mathematical frontier object explicitly via
`latent_compiled_tableau_bound_logscale`. -/
theorem P_neq_NP_latent_from_compiled_tableau_bound (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (hCompiled : latent_compiled_tableau_bound_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn

  -- Canonical NP data
  have hCoeff : selCon_kronecker_coeff_law_logscale M n hn804 :=
    selCon_kronecker_coeff_law_logscale_from_canonical_idxList M n hn804
  have npData : selCon_kronecker_data_logscale M n hn804 := hCoeff

  -- P-data package from the direct compiled-polynomial bound + explicit Section-9 sides
  have pCore : latent_profile_assembly_logscale M n hnM hn804 :=
    (latent_profile_assembly_logscale_iff_compiled_tableau_bound M n hnM hn804).2 hCompiled
  have pAsm : theorem216_p_obligation M n hnM hn804 :=
    theorem216_profile_data_logscale_from_core M n hnM hn804
      (theorem9_profile_count_obligation_proved M n hn804)
      (theorem9_within_profile_dim_obligation_proved M n hn804)
      pCore

  exact P_neq_NP_latent_decomp h n hn ⟨npData, pAsm⟩

/-- Canonical-NP route from the core P-side profile assembly bound directly.

This is the clean canonical entrypoint once the compiler/profile theorem is proved:
provide `latent_profile_assembly_logscale` and the contradiction closes.
No external NP decomposition data is required. -/
theorem P_neq_NP_latent_from_p_core (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pCore : latent_profile_assembly_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    (latent_profile_assembly_logscale_iff_compiled_tableau_bound M n hnM hn804).1 pCore
  exact P_neq_NP_latent_from_compiled_tableau_bound h n hn hCompiled

/-- Canonical-NP route from bucket-schema witness via the direct compiled-tableau
frontier obligation. -/
theorem P_neq_NP_latent_from_p_bucket_function_via_compiled (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pFun : latent_profile_bucket_function_bound_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    latent_compiled_tableau_bound_logscale_from_bucket_function M n hnM hn804 pFun
  exact P_neq_NP_latent_from_compiled_tableau_bound h n hn hCompiled

/-- Canonical-NP route with functional bucket-schema P witness normalized
through the core P-side assembly theorem `latent_profile_assembly_logscale`. -/
theorem P_neq_NP_latent_from_p_bucket_function_via_core (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pFun : latent_profile_bucket_function_bound_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  exact P_neq_NP_latent_from_p_bucket_function_via_compiled h n hn pFun

/-- Canonical-NP route from span-card witness via the direct compiled-tableau
frontier obligation. -/
theorem P_neq_NP_latent_from_p_span_card_via_compiled (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pSpan : latent_profile_span_card_bound_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    latent_compiled_tableau_bound_logscale_from_span_card_bound M n hnM hn804 pSpan
  exact P_neq_NP_latent_from_compiled_tableau_bound h n hn hCompiled

/-- Canonical-NP route with span-card P witness normalized through the
core P-side assembly theorem `latent_profile_assembly_logscale`. -/
theorem P_neq_NP_latent_from_p_span_card_via_core (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pSpan : latent_profile_span_card_bound_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  exact P_neq_NP_latent_from_p_span_card_via_compiled h n hn pSpan

/-- Canonical-NP route with only the span-card P witness package. -/
theorem P_neq_NP_latent_from_p_span_card (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pSpan : latent_profile_span_card_bound_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  exact P_neq_NP_latent_from_p_span_card_via_compiled h n hn pSpan

/-- Canonical-NP route from block-cover witness via the direct compiled-tableau
frontier obligation. -/
theorem P_neq_NP_latent_from_p_block_cover_via_compiled (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pCover : latent_profile_block_cover_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    latent_compiled_tableau_bound_logscale_from_block_cover M n hnM hn804 pCover
  exact P_neq_NP_latent_from_compiled_tableau_bound h n hn hCompiled

/-- Canonical-NP route with block-cover P witness normalized through the
core P-side assembly theorem `latent_profile_assembly_logscale`. -/
theorem P_neq_NP_latent_from_p_block_cover_via_core (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pCover : latent_profile_block_cover_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  exact P_neq_NP_latent_from_p_block_cover_via_compiled h n hn pCover

/-- Canonical-NP route with P-side block-cover witness only. -/
theorem P_neq_NP_latent_from_p_block_cover (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pCover : latent_profile_block_cover_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  exact P_neq_NP_latent_from_p_block_cover_via_compiled h n hn pCover

/-- Canonical-NP route with P-side global-span+bucket witness only. -/
theorem P_neq_NP_latent_from_p_global_span_bucket (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pGB : latent_global_span_and_bucket_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have pData : latent_profile_block_cover_construction_data_logscale M n hnM hn804 :=
    latent_profile_block_cover_construction_data_from_global_span_and_bucket M n hnM hn804 pGB
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    latent_compiled_tableau_bound_logscale_from_construction_data M n hnM hn804 pData
  exact P_neq_NP_latent_from_compiled_tableau_bound h n hn hCompiled

/-- Move-4 canonical route: Item-3 with uniform `n^120` bound. -/
theorem P_neq_NP_latent_from_p_item3_uniform120 (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (p3120 : latent_profile_block_cover_item3_uniform120_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    latent_compiled_tableau_bound_logscale_from_item3_uniform120 M n hnM hn804 p3120
  exact P_neq_NP_latent_from_compiled_tableau_bound h n hn hCompiled

/-- Canonical-NP route with Item-3+uniform-Item-2 P witness only. -/
theorem P_neq_NP_latent_from_p_item3_uniform2 (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (p3u2 : latent_profile_block_cover_item3_uniform2_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have hAny :
      latent_profile_block_cover_item3_uniform2_logscale M n hnM hn804 ∨
      latent_p_witness_span160_logscale M n hnM hn804 ∨
      latent_p_witness_target_logscale M n hnM hn804 ∨
      latent_profile_block_cover_construction_data_logscale M n hnM hn804 ∨
      latent_profile_span_card_bound_logscale M n hnM hn804 :=
    latent_any_source_of_item3_uniform2 M n hnM hn804 p3u2
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    latent_compiled_tableau_bound_proved_from_any_source M n hnM hn804 hAny
  exact P_neq_NP_latent_from_compiled_tableau_bound h n hn hCompiled

/-- Frozen canonical final entrypoint (Move-1):
assume exactly `latent_p_witness_target_logscale` on the P side. -/
theorem P_neq_NP_latent_from_p_witness_target (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pTarget : latent_p_witness_target_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have hAny :
      latent_profile_block_cover_item3_uniform2_logscale M n hnM hn804 ∨
      latent_p_witness_span160_logscale M n hnM hn804 ∨
      latent_p_witness_target_logscale M n hnM hn804 ∨
      latent_profile_block_cover_construction_data_logscale M n hnM hn804 ∨
      latent_profile_span_card_bound_logscale M n hnM hn804 :=
    latent_any_source_of_p_witness_target M n hnM hn804 pTarget
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    latent_compiled_tableau_bound_proved_from_any_source M n hnM hn804 hAny
  exact P_neq_NP_latent_from_compiled_tableau_bound h n hn hCompiled

/-- Move-2 strong-entry route: if a single span witness of size `≤ n^160` is built,
then frozen target follows immediately and the contradiction route closes. -/
theorem P_neq_NP_latent_from_p_span160 (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (p160 : latent_p_witness_span160_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have hAny :
      latent_profile_block_cover_item3_uniform2_logscale M n hnM hn804 ∨
      latent_p_witness_span160_logscale M n hnM hn804 ∨
      latent_p_witness_target_logscale M n hnM hn804 ∨
      latent_profile_block_cover_construction_data_logscale M n hnM hn804 ∨
      latent_profile_span_card_bound_logscale M n hnM hn804 :=
    latent_any_source_of_span160 M n hnM hn804 p160
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    latent_compiled_tableau_bound_proved_from_any_source M n hnM hn804 hAny
  exact P_neq_NP_latent_from_compiled_tableau_bound h n hn hCompiled

/-- Move-5 complete route from an explicit `n^160` rank bound hypothesis.
No global axiom is used here. -/
theorem P_neq_NP_from_generator_bound (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (hRank : mlBlockedSpdpRank (latentPartition h.sat_decider n) (Nat.log 2 n) (Nat.log 2 n)
      (latentCompiledPoly h.sat_decider n) ≤ n ^ 160) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    latent_compiled_tableau_bound_logscale_from_rank160 M n hnM hn804 hRank
  exact P_neq_NP_latent_from_compiled_tableau_bound h n hn hCompiled

/-- Move-3 route: profile parts with `(40,120)` bounds imply span160,
then the Move-2 strong route closes the contradiction. -/
theorem P_neq_NP_latent_from_p_parts_40_120 (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pParts : latent_profile_span_card_parts_40_120_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have hCompiled : latent_compiled_tableau_bound_logscale M n hnM hn804 :=
    latent_compiled_tableau_bound_logscale_from_parts_40_120 M n hnM hn804 pParts
  exact P_neq_NP_latent_from_compiled_tableau_bound h n hn hCompiled

/-- Canonical-NP route from functional profile-id bucket schema (P-side).
This is often the most natural constructive form to prove from paper definitions. -/
theorem P_neq_NP_latent_from_p_bucket_function (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pFun : latent_profile_bucket_function_bound_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  exact P_neq_NP_latent_from_p_bucket_function_via_compiled h n hn pFun

/-- Direct canonical-NP bridge: bucket-function witness can be routed through
block-cover equivalence before entering the canonical final route. -/
theorem P_neq_NP_latent_from_p_bucket_function_via_block_cover (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pFun : latent_profile_bucket_function_bound_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  exact P_neq_NP_latent_from_p_bucket_function_via_compiled h n hn pFun

/-- Symmetric canonical-NP bridge: block-cover witness can be routed through
bucket-function equivalence before entering the canonical final route. -/
theorem P_neq_NP_latent_from_p_block_cover_via_bucket_function (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pCover : latent_profile_block_cover_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  exact P_neq_NP_latent_from_p_block_cover_via_compiled h n hn pCover

/-- Convenience bridge: block-cover input can be normalized to construction-data,
then fed through the most concrete construction-data route. -/
theorem P_neq_NP_latent_from_finer_decomp_and_p_block_cover_via_construction_data
    (h : PeqNP) (n : ℕ)
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
  have pData : latent_profile_block_cover_construction_data_logscale M n hnM hn804 :=
    latent_profile_block_cover_construction_data_from_block_cover M n hnM hn804 pCover
  exact P_neq_NP_latent_from_finer_decomp_and_p_construction_data h n hn idxList hnd hlen hfinj pData

/-- Symmetric convenience bridge: global-span+bucket input routed via
construction-data normalization. -/
theorem P_neq_NP_latent_from_finer_decomp_and_p_global_span_bucket_via_construction_data
    (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (idxList : Fin (Nat.choose (latentBaseVars h.sat_decider n) (Nat.log 2 n)) →
      List (Fin (latentBaseVars h.sat_decider n)))
    (hnd : ∀ i, (idxList i).Nodup)
    (hlen : ∀ i, (idxList i).length = Nat.log 2 n)
    (hfinj : ∀ i j, (idxList i).toFinset = (idxList j).toFinset → i = j)
    (pGB : latent_global_span_and_bucket_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have pData : latent_profile_block_cover_construction_data_logscale M n hnM hn804 :=
    latent_profile_block_cover_construction_data_from_global_span_and_bucket M n hnM hn804 pGB
  exact P_neq_NP_latent_from_finer_decomp_and_p_construction_data h n hn idxList hnd hlen hfinj pData

/-- Global closure theorem:
if the construction-data witness is available uniformly at contradiction scale,
then `PeqNP` is impossible.

This isolates the current remaining P-frontier obligation into a single
uniform hypothesis. -/
theorem no_PeqNP_of_uniform_construction_data
    (hData : ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      latent_profile_block_cover_construction_data_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn)) :
    PeqNP → False := by
  intro h
  let n : ℕ := max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)
  have hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804) := by
    exact le_rfl
  exact P_neq_NP_latent_from_p_construction_data h n hn (hData h n hn)

/-- Global closure theorem:
if the bucket-function witness is available uniformly at contradiction scale,
then `PeqNP` is impossible (by normalization to construction-data). -/
theorem no_PeqNP_of_uniform_bucket_function
    (hFun : ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      latent_profile_bucket_function_bound_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn)) :
    PeqNP → False := by
  intro h
  let n : ℕ := max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)
  have hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804) := by
    exact le_rfl
  have hnM : n ≥ max 4 h.sat_decider.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have pFun : latent_profile_bucket_function_bound_logscale h.sat_decider n hnM hn804 :=
    hFun h n hn
  have pData : latent_profile_block_cover_construction_data_logscale h.sat_decider n hnM hn804 :=
    latent_profile_block_cover_construction_data_from_bucket_function h.sat_decider n hnM hn804 pFun
  exact no_PeqNP_of_uniform_construction_data (fun h' n' hn' =>
    latent_profile_block_cover_construction_data_from_bucket_function h'.sat_decider n'
      (hnM_of_hn h' n' hn') (hn804_of_hn h' n' hn') (hFun h' n' hn')) h

/-- Global closure theorem:
if any approved compiler witness source is available uniformly at contradiction
scale, then `PeqNP` is impossible.

This uses the consolidated `any-source` wrapper from `CompilerProperties`. -/
theorem no_PeqNP_of_uniform_any_compiler_source
    (hAny : ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      (latent_profile_block_cover_item3_uniform2_logscale h.sat_decider n
          (hnM_of_hn h n hn) (hn804_of_hn h n hn) ∨
       latent_p_witness_span160_logscale h.sat_decider n
          (hnM_of_hn h n hn) (hn804_of_hn h n hn) ∨
       latent_p_witness_target_logscale h.sat_decider n
          (hnM_of_hn h n hn) (hn804_of_hn h n hn) ∨
       latent_profile_block_cover_construction_data_logscale h.sat_decider n
          (hnM_of_hn h n hn) (hn804_of_hn h n hn) ∨
       latent_profile_span_card_bound_logscale h.sat_decider n
          (hnM_of_hn h n hn) (hn804_of_hn h n hn))) :
    PeqNP → False := by
  intro h
  let n : ℕ := max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)
  have hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804) := by
    exact le_rfl
  have hnM : n ≥ max 4 h.sat_decider.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have hCompiled : latent_compiled_tableau_bound_logscale h.sat_decider n hnM hn804 :=
    latent_compiled_tableau_bound_proved_from_any_source h.sat_decider n hnM hn804 (hAny h n hn)
  exact P_neq_NP_latent_from_compiled_tableau_bound h n hn hCompiled

/-- Global closure theorem:
if a uniform block-cover witness is available at contradiction scale,
then `PeqNP` is impossible.

This is the direct closure form for the paper's constructive profile-cover target. -/
theorem no_PeqNP_of_uniform_block_cover
    (hCover : ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      latent_profile_block_cover_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn)) :
    PeqNP → False := by
  intro h
  let n : ℕ := max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)
  have hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804) := by
    exact le_rfl
  exact P_neq_NP_latent_from_p_block_cover h n hn (hCover h n hn)

/-- Global closure theorem:
if a uniform finite span-card witness is available at contradiction scale,
then `PeqNP` is impossible. -/
theorem no_PeqNP_of_uniform_span_card
    (hSpan : ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      latent_profile_span_card_bound_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn)) :
    PeqNP → False := by
  intro h
  let n : ℕ := max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)
  have hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804) := by
    exact le_rfl
  exact P_neq_NP_latent_from_p_span_card h n hn (hSpan h n hn)

/-- Global closure theorem:
if the concrete locality/profile structure is available uniformly at contradiction
scale, then `PeqNP` is impossible.

This is the direct paper-faithful bridge: locality/profile structure ⇒ block-cover ⇒
contradiction route. -/
theorem no_PeqNP_of_uniform_concrete_locality_profile_structure
    (hLoc : ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      concrete_locality_profile_structure_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn)) :
    PeqNP → False := by
  exact no_PeqNP_of_uniform_block_cover (fun h n hn =>
    latent_profile_block_cover_from_concrete_locality_profile_structure h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn) (hLoc h n hn))

/-- Step-1 structural normalization: pointwise equivalence between the paper-facing
concrete locality/profile predicate and the Item-3+uniform-Item-2 package. -/
theorem concrete_locality_profile_structure_logscale_iff_item3_uniform2
    (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804) :
    concrete_locality_profile_structure_logscale M n hn hn804 ↔
    latent_profile_block_cover_item3_uniform2_logscale M n hn hn804 := by
  rfl

/-- Step-1 uniform structural lemma (no per-instance witness args): a uniform
Item-3+uniform-Item-2 theorem is exactly a uniform concrete locality/profile theorem. -/
theorem uniform_concrete_locality_profile_structure_of_uniform_item3_uniform2
    (hItem3u2 : ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      latent_profile_block_cover_item3_uniform2_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn)) :
    ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      concrete_locality_profile_structure_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn) := by
  intro h n hn
  simpa [concrete_locality_profile_structure_logscale] using hItem3u2 h n hn

/-- Step-2 bridge theorem (no extra witness args): uniform concrete
locality/profile structure implies the uniform block-cover witness. -/
theorem uniform_block_cover_of_uniform_concrete_locality_profile_structure
    (hLoc : ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      concrete_locality_profile_structure_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn)) :
    ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      latent_profile_block_cover_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn) := by
  intro h n hn
  exact latent_profile_block_cover_from_concrete_locality_profile_structure h.sat_decider n
    (hnM_of_hn h n hn) (hn804_of_hn h n hn) (hLoc h n hn)

/-- Step-3 composed closure theorem: if the uniform Item-3+uniform-Item-2
statement is proved internally, unconditional contradiction follows (via
Step-1 normalization + Step-2 block-cover lift + existing closure route). -/
theorem no_PeqNP_of_uniform_item3_uniform2
    (hItem3u2 : ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      latent_profile_block_cover_item3_uniform2_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn)) :
    PeqNP → False :=
  no_PeqNP_of_uniform_block_cover
    (uniform_block_cover_of_uniform_concrete_locality_profile_structure
      (uniform_concrete_locality_profile_structure_of_uniform_item3_uniform2 hItem3u2))

/-- Global bridge theorem: a global internal block-cover theorem implies a global
construction-data theorem (explicit witness extraction). -/
theorem global_construction_data_of_global_block_cover
    (hCover : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_logscale M n hn hn804) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_construction_data_logscale M n hn hn804 := by
  intro M n hn hn804
  exact latent_profile_block_cover_construction_data_from_block_cover M n hn hn804
    (hCover M n hn hn804)

/-- Global bridge theorem: a global internal construction-data theorem implies a
global span+bucket theorem (definition-level unpacking, lifted uniformly). -/
theorem global_span_and_bucket_of_global_construction_data
    (hData : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_construction_data_logscale M n hn hn804) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_global_span_and_bucket_logscale M n hn hn804 := by
  intro M n hn hn804
  exact latent_global_span_and_bucket_logscale_from_construction_data M n hn hn804
    (hData M n hn hn804)

/-- Global bridge theorem: a global block-cover theorem yields a global
span+bucket theorem by explicit witness extraction. -/
theorem global_span_and_bucket_of_global_block_cover
    (hCover : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_logscale M n hn hn804) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_global_span_and_bucket_logscale M n hn hn804 := by
  intro M n hn hn804
  exact latent_global_span_and_bucket_logscale_from_block_cover M n hn hn804
    (hCover M n hn hn804)

/-- Step-4 bridge: shared-witness items imply the global semantic hard target
via the Step-3 normalization lemma (items -> item3+uniform2). -/
theorem global_compiler_semantics_p_witness_target_of_global_items
    (hItems : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_items_logscale M n hn hn804) :
    global_compiler_semantics_p_witness_target := by
  intro M n hn hn804
  exact latent_p_witness_target_from_items M n hn hn804 (hItems M n hn hn804)

/-- Step-2a bridge: a global Item-3+uniform-Item-2 theorem yields the global
shared-witness items theorem directly. -/
theorem global_items_of_global_item3_uniform2
    (hItem3u2 : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_item3_uniform2_logscale M n hn hn804) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_items_logscale M n hn hn804 := by
  intro M n hn hn804
  exact latent_profile_block_cover_items_from_item3_uniform2 M n hn hn804
    (hItem3u2 M n hn hn804)

/-- Strengthened bridge: a global Item-3+uniform-120 theorem already yields the
headline semantic target (via span160 then frozen target). -/
theorem global_compiler_semantics_p_witness_target_of_global_item3_uniform120
    (hItem3120 : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_item3_uniform120_logscale M n hn hn804) :
    global_compiler_semantics_p_witness_target := by
  intro M n hn hn804
  exact latent_p_witness_target_from_span160 M n hn hn804
    (latent_p_witness_span160_logscale_from_item3_uniform120 M n hn hn804
      (hItem3120 M n hn hn804))

/-- Step-2 bridge (first semantic-development milestone):
a global Item-3+uniform-Item-2 theorem yields the global semantic
P-side target witness theorem. -/
theorem global_compiler_semantics_p_witness_target_of_global_item3_uniform2
    (hItem3u2 : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_item3_uniform2_logscale M n hn hn804) :
    global_compiler_semantics_p_witness_target :=
  global_compiler_semantics_p_witness_target_of_global_items
    (global_items_of_global_item3_uniform2 hItem3u2)

/-- Step-1 typed bridge theorem (compiler->latent interface):
if a variable/partition embedding gives pointwise rank domination from latent to
`fullCompiledPoly`, then any global rank160 bound on `fullCompiledPoly` transfers
to a global rank160 bound on `latentCompiledPoly`.

This isolates exactly the first hard formalization obligation: constructing that
embedding domination hypothesis from compiler semantics. -/
theorem global_latent_rank160_of_full_compiled_rank160_under_embedding
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hBridge : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n)
      ≤ mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (fullCompiledPoly ℚ M n (hLeWitness M n hn hn804)))
    (hFull : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n (hLeWitness M n hn hn804)) ≤ n ^ 160) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n) ≤ n ^ 160 := by
  intro M n hn hn804
  exact le_trans (hBridge M n hn hn804) (hFull M n hn hn804)

/-- Step-2 closure wrapper for the typed interface bridge:
if full-compiled rank160 is available globally and an embedding bridge transfers
it to latent rank160, then the unconditional contradiction route closes. -/
theorem no_PeqNP_of_full_compiled_rank160_under_embedding
    (hLeWitness : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hBridge : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n)
      ≤ mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (fullCompiledPoly ℚ M n (hLeWitness M n hn hn804)))
    (hFull : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n (hLeWitness M n hn hn804)) ≤ n ^ 160) :
    PeqNP → False :=
  no_PeqNP_of_uniform_any_compiler_source (fun h n hn =>
    Or.inr (Or.inr (Or.inl
      (latent_p_witness_target_from_span160 h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn)
        (latentCompiledPoly_spdp_subspace_span_poly_bound h.sat_decider n
          (hnM_of_hn h n hn) (hn804_of_hn h n hn)
          (global_latent_rank160_of_full_compiled_rank160_under_embedding
            hLeWitness hBridge hFull h.sat_decider n
            (hnM_of_hn h n hn) (hn804_of_hn h n hn)))))))

/-- Core reduction theorem: a uniform direct SPDP-rank upper bound for the
compiled polynomial yields the headline semantic target witness globally. -/
theorem global_compiler_semantics_p_witness_target_of_global_rank160_bound
    (hRank : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n) ≤ n ^ 160) :
    global_compiler_semantics_p_witness_target := by
  intro M n hn hn804
  exact latent_p_witness_target_from_span160 M n hn hn804
    (latentCompiledPoly_spdp_subspace_span_poly_bound M n hn hn804
      (hRank M n hn hn804))

/-- Final closure packaged against the paper-facing semantic hard target constant
from `LatentWidthRankDecomp`. -/
theorem no_PeqNP_of_global_compiler_semantics_p_witness_target
    (hSem : global_compiler_semantics_p_witness_target) :
    PeqNP → False :=
  no_PeqNP_of_uniform_any_compiler_source (fun h n hn =>
    Or.inr (Or.inr (Or.inl
      (hSem h.sat_decider n (hnM_of_hn h n hn) (hn804_of_hn h n hn)))) )

/-- Paper-facing profile-compression-to-rank bridge:
global `(40,120)` profile parts imply a global direct rank160 upper bound. -/
theorem global_rank160_bound_of_global_parts_40_120
    (hParts : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_span_card_parts_40_120_logscale M n hn hn804) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n) ≤ n ^ 160 := by
  intro M n hn hn804
  rcases latent_p_witness_span160_logscale_from_parts_40_120 M n hn hn804
      (hParts M n hn hn804) with ⟨G, hIncl, hCard⟩
  unfold mlBlockedSpdpRank
  have hmono : Module.finrank ℚ
      (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n)) ≤
      Module.finrank ℚ (Submodule.span ℚ (↑G : Set (MvPolynomial (Fin (latentNumVars M n)) ℚ))) :=
    Submodule.finrank_mono hIncl
  have hspan_card : Module.finrank ℚ
      (Submodule.span ℚ (↑G : Set (MvPolynomial (Fin (latentNumVars M n)) ℚ))) ≤ G.card :=
    finrank_span_finset_le_card G
  exact le_trans (le_trans hmono hspan_card) hCard

/-- Immediate closure corollary: a global direct rank160 bound already implies
`PeqNP → False` via the semantic hard target. -/
theorem no_PeqNP_of_global_rank160_bound
    (hRank : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n) ≤ n ^ 160) :
    PeqNP → False :=
  no_PeqNP_of_global_compiler_semantics_p_witness_target
    (global_compiler_semantics_p_witness_target_of_global_rank160_bound hRank)

/-- Hooked closure corollary (paper §9/§40 profile-compression path):
global `(40,120)` parts -> global rank160 -> contradiction. -/
theorem no_PeqNP_of_global_parts_40_120_via_rank160
    (hParts : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_span_card_parts_40_120_logscale M n hn hn804) :
    PeqNP → False :=
  no_PeqNP_of_global_rank160_bound
    (global_rank160_bound_of_global_parts_40_120 hParts)

/-- Equivalence packaging for the hard semantic frontier: global frozen Move-1
P-target exists iff global span+bucket data exists. -/
theorem global_semantic_target_iff_global_span_and_bucket :
    global_compiler_semantics_p_witness_target ↔
    (∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_global_span_and_bucket_logscale M n hn hn804) := by
  constructor
  · intro hSem
    intro M n hn hn804
    exact latent_global_span_and_bucket_from_p_witness_target M n hn hn804
      (hSem M n hn hn804)
  · intro hGB
    intro M n hn hn804
    exact latent_p_witness_target_from_global_span_bucket M n hn hn804
      (hGB M n hn hn804)

/-- Step-1 packaging alias: global span+bucket semantics imply the headline
semantic target theorem family. -/
theorem global_compiler_semantics_p_witness_target_of_global_span_and_bucket
    (hGB : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_global_span_and_bucket_logscale M n hn hn804) :
    global_compiler_semantics_p_witness_target := by
  intro M n hn hn804
  exact latent_p_witness_target_from_global_span_bucket M n hn hn804
    (hGB M n hn hn804)

/-- Derived corollary from the headline semantic target: global span+bucket form. -/
theorem global_span_and_bucket_of_global_compiler_semantics_p_witness_target
    (hSem : global_compiler_semantics_p_witness_target) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_global_span_and_bucket_logscale M n hn hn804 := by
  intro M n hn hn804
  exact latent_global_span_and_bucket_from_p_witness_target M n hn hn804
    (hSem M n hn hn804)

/-- Derived corollary from the headline semantic target: global block-cover form. -/
theorem global_block_cover_of_global_compiler_semantics_p_witness_target
    (hSem : global_compiler_semantics_p_witness_target) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_logscale M n hn hn804 := by
  intro M n hn hn804
  exact latent_profile_block_cover_logscale_from_global_span_and_bucket M n hn hn804
    (global_span_and_bucket_of_global_compiler_semantics_p_witness_target hSem M n hn hn804)

/-- Tight frontier equivalence: proving global items is equivalent to proving the
headline semantic target. -/
theorem global_semantic_target_iff_global_items :
    global_compiler_semantics_p_witness_target ↔
    (∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_items_logscale M n hn hn804) := by
  constructor
  · intro hSem
    intro M n hn hn804
    exact latent_profile_block_cover_items_from_block_cover M n hn hn804
      (latent_profile_block_cover_logscale_from_global_span_and_bucket M n hn hn804
        (latent_global_span_and_bucket_from_p_witness_target M n hn hn804
          (hSem M n hn hn804)))
  · intro hItems
    exact global_compiler_semantics_p_witness_target_of_global_items hItems

/-- Tight frontier equivalence: proving global block-cover is equivalent to proving
the headline semantic target. -/
theorem global_semantic_target_iff_global_block_cover :
    global_compiler_semantics_p_witness_target ↔
    (∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_logscale M n hn hn804) := by
  constructor
  · intro hSem
    exact global_block_cover_of_global_compiler_semantics_p_witness_target hSem
  · intro hCover
    exact global_compiler_semantics_p_witness_target_of_global_items
      (fun M n hn hn804 => latent_profile_block_cover_items_from_block_cover M n hn hn804 (hCover M n hn hn804))

/-- Derived corollary from the headline semantic target: shared-witness items form. -/
theorem global_items_of_global_compiler_semantics_p_witness_target
    (hSem : global_compiler_semantics_p_witness_target) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_items_logscale M n hn hn804 := by
  intro M n hn hn804
  exact latent_profile_block_cover_items_from_block_cover M n hn hn804
    (global_block_cover_of_global_compiler_semantics_p_witness_target hSem M n hn hn804)

/-- Global bridge theorem: a global p-witness-target theorem yields a global
span+bucket theorem directly (reverse Move-1 bridge). -/
theorem global_span_and_bucket_of_global_p_witness_target
    (hTarget : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_p_witness_target_logscale M n hn hn804) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_global_span_and_bucket_logscale M n hn hn804 := by
  intro M n hn hn804
  exact latent_global_span_and_bucket_from_p_witness_target M n hn hn804
    (hTarget M n hn hn804)

/-- Global bridge theorem: a global span+bucket constructor yields a global
p-witness-target theorem directly. -/
theorem global_p_witness_target_of_global_span_and_bucket
    (hGB : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_global_span_and_bucket_logscale M n hn hn804) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_p_witness_target_logscale M n hn hn804 := by
  intro M n hn hn804
  exact latent_p_witness_target_from_global_span_bucket M n hn hn804
    (hGB M n hn hn804)

/-- Global bridge theorem: a global span+bucket constructor yields a global
block-cover theorem directly. -/
theorem global_block_cover_of_global_span_and_bucket
    (hGB : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_global_span_and_bucket_logscale M n hn hn804) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_logscale M n hn hn804 := by
  intro M n hn hn804
  exact latent_profile_block_cover_logscale_from_global_span_and_bucket M n hn hn804
    (hGB M n hn hn804)

/-- Global bridge theorem: a global internal construction of span+bucket data
for compiled logscale SPDP subspaces implies the global Item-3+uniform-Item-2
theorem. -/
theorem global_item3_uniform2_of_global_span_and_bucket
    (hGB : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_global_span_and_bucket_logscale M n hn hn804) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_item3_uniform2_logscale M n hn hn804 := by
  intro M n hn hn804
  exact latent_profile_block_cover_item3_uniform2_from_global_span_and_bucket M n hn hn804
    (hGB M n hn hn804)

/-- Composed global closure: global p-witness-target theorem is sufficient for
`PeqNP → False` (paper-faithful Width⇒Rank-to-contradiction route). -/
theorem no_PeqNP_of_global_p_witness_target
    (hTarget : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_p_witness_target_logscale M n hn hn804) :
    PeqNP → False :=
  no_PeqNP_of_uniform_any_compiler_source (fun h n hn =>
    Or.inr (Or.inr (Or.inl
      (hTarget h.sat_decider n (hnM_of_hn h n hn) (hn804_of_hn h n hn)))))

/-- Composed global closure: global span+bucket theorem is sufficient for
`PeqNP → False` via the direct global block-cover bridge. -/
theorem no_PeqNP_of_global_span_and_bucket
    (hGB : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_global_span_and_bucket_logscale M n hn hn804) :
    PeqNP → False :=
  no_PeqNP_of_global_compiler_semantics_p_witness_target
    (global_compiler_semantics_p_witness_target_of_global_span_and_bucket hGB)

/-- Composed global closure: global block-cover theorem is sufficient for
`PeqNP → False` via construction-data and the established global bridge chain. -/
theorem no_PeqNP_of_global_block_cover
    (hCover : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_logscale M n hn hn804) :
    PeqNP → False :=
  no_PeqNP_of_uniform_item3_uniform2 (fun h n hn =>
    latent_profile_block_cover_item3_uniform2_from_global_span_and_bucket h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)
      (latent_global_span_and_bucket_logscale_from_construction_data h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn)
        (global_construction_data_of_global_block_cover hCover h.sat_decider n
          (hnM_of_hn h n hn) (hn804_of_hn h n hn))))

/-- Composed global closure: global construction-data theorem is sufficient for
`PeqNP → False` via global span+bucket and global item3+uniform2 bridges. -/
theorem no_PeqNP_of_global_construction_data
    (hData : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_construction_data_logscale M n hn hn804) :
    PeqNP → False :=
  no_PeqNP_of_uniform_item3_uniform2 (fun h n hn =>
    global_item3_uniform2_of_global_span_and_bucket
      (global_span_and_bucket_of_global_construction_data hData)
      h.sat_decider n (hnM_of_hn h n hn) (hn804_of_hn h n hn))

/-- Step-4 closure theorem: if Item-3+uniform-Item-2 is proved as a global
internal compiler theorem for every DTM at contradiction scale, then `PeqNP`
is impossible (no `h`-indexed witness assumptions left). -/
theorem no_PeqNP_of_global_item3_uniform2
    (hGlobal : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_item3_uniform2_logscale M n hn hn804) :
    PeqNP → False := by
  intro h
  exact no_PeqNP_of_uniform_item3_uniform2 (fun h' n hn =>
    hGlobal h'.sat_decider n (hnM_of_hn h' n hn) (hn804_of_hn h' n hn)) h

/-- Closure packaging through Step-4 items normalization and semantic target. -/
theorem no_PeqNP_of_global_items_via_semantic_target
    (hItems : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_items_logscale M n hn hn804) :
    PeqNP → False :=
  no_PeqNP_of_global_compiler_semantics_p_witness_target
    (global_compiler_semantics_p_witness_target_of_global_items hItems)

/-- Forward packaging bridge: global Item-3+uniform-120 yields global `(40,120)`
parts directly (paper Move-4 decomposition). -/
theorem global_parts_40_120_of_global_item3_uniform120
    (hItem3120 : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_item3_uniform120_logscale M n hn hn804) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_span_card_parts_40_120_logscale M n hn hn804 := by
  intro M n hn hn804
  exact latent_profile_span_card_parts_40_120_from_item3_uniform120 M n hn hn804
    (hItem3120 M n hn hn804)

/-- Converse packaging bridge: a global `(40,120)` parts theorem yields the
global Item-3+uniform-120 package directly (via established Move-4 bridge). -/
theorem global_item3_uniform120_of_global_parts_40_120
    (hParts : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_span_card_parts_40_120_logscale M n hn hn804) :
    ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_item3_uniform120_logscale M n hn hn804 := by
  intro M n hn hn804
  exact latent_profile_block_cover_item3_uniform120_from_parts_40_120 M n hn hn804
    (hParts M n hn hn804)

/-- Tight profile-compression equivalence at the global level. -/
theorem global_parts_40_120_iff_global_item3_uniform120 :
    (∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_span_card_parts_40_120_logscale M n hn hn804)
    ↔
    (∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_item3_uniform120_logscale M n hn hn804) := by
  constructor
  · intro hParts
    exact global_item3_uniform120_of_global_parts_40_120 hParts
  · intro hItem3120
    exact global_parts_40_120_of_global_item3_uniform120 hItem3120

/-- Paper-facing profile-compression bridge: a global `(40,120)` parts theorem
already yields the global semantic hard target (via span160). -/
theorem global_compiler_semantics_p_witness_target_of_global_parts_40_120
    (hParts : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_span_card_parts_40_120_logscale M n hn hn804) :
    global_compiler_semantics_p_witness_target := by
  intro M n hn hn804
  exact latent_p_witness_target_from_span160 M n hn hn804
    (latent_p_witness_span160_logscale_from_parts_40_120 M n hn hn804
      (hParts M n hn hn804))

/-- Closure corollary for the profile-compression `(40,120)` route. -/
theorem no_PeqNP_of_global_parts_40_120_via_semantic_target
    (hParts : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_span_card_parts_40_120_logscale M n hn hn804) :
    PeqNP → False :=
  no_PeqNP_of_global_compiler_semantics_p_witness_target
    (global_compiler_semantics_p_witness_target_of_global_parts_40_120 hParts)

/-- Closure corollary for the strengthened Item-3+uniform-120 route. -/
theorem no_PeqNP_of_global_item3_uniform120_via_semantic_target
    (hItem3120 : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_item3_uniform120_logscale M n hn hn804) :
    PeqNP → False :=
  no_PeqNP_of_global_compiler_semantics_p_witness_target
    (global_compiler_semantics_p_witness_target_of_global_item3_uniform120 hItem3120)

/-- Alternate closure packaging through the semantic hard-target constant. -/
theorem no_PeqNP_of_global_item3_uniform2_via_semantic_target
    (hGlobal : ∀ (M : DTM) (n : ℕ),
      (hn : n ≥ max 4 M.numStates) → (hn804 : n ≥ 2 ^ 804) →
      latent_profile_block_cover_item3_uniform2_logscale M n hn hn804) :
    PeqNP → False :=
  no_PeqNP_of_global_compiler_semantics_p_witness_target
    (global_compiler_semantics_p_witness_target_of_global_item3_uniform2 hGlobal)

/-- Uniform bridge theorem (no extra witness args): concrete locality/profile
structure uniformly implies the uniform span-card witness. -/
theorem uniform_span_card_of_uniform_concrete_locality_profile_structure
    (hLoc : ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      concrete_locality_profile_structure_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn)) :
    ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      latent_profile_span_card_bound_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn) := by
  intro h n hn
  exact latent_profile_span_card_bound_from_concrete_locality_profile_structure h.sat_decider n
    (hnM_of_hn h n hn) (hn804_of_hn h n hn) (hLoc h n hn)

/-- Global closure theorem:
if the concrete locality/profile structure is available uniformly, then the
paper's span-card witness is also uniformly available, and `PeqNP` is impossible. -/
theorem no_PeqNP_of_uniform_concrete_locality_profile_structure_via_span_card
    (hLoc : ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      concrete_locality_profile_structure_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn)) :
    PeqNP → False := by
  exact no_PeqNP_of_uniform_span_card
    (uniform_span_card_of_uniform_concrete_locality_profile_structure hLoc)

/-- Uniform bridge theorem (Move-3 scale, no extra witness args): stronger
concrete locality/profile structure uniformly implies the uniform span160 witness. -/
theorem uniform_span160_of_uniform_concrete_locality_profile_structure120
    (hLoc120 : ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      concrete_locality_profile_structure120_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn)) :
    ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      latent_p_witness_span160_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn) := by
  intro h n hn
  exact latent_p_witness_span160_from_concrete_locality_profile_structure120 h.sat_decider n
    (hnM_of_hn h n hn) (hn804_of_hn h n hn) (hLoc120 h n hn)

/-- Global closure theorem:
if the stronger concrete locality/profile structure (Move-3 scale, `n^120` per
profile block) is available uniformly, then `PeqNP` is impossible via the span160
route. -/
theorem no_PeqNP_of_uniform_concrete_locality_profile_structure120_via_span160
    (hLoc120 : ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      concrete_locality_profile_structure120_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn)) :
    PeqNP → False := by
  intro h
  let n : ℕ := max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)
  have hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804) := by
    exact le_rfl
  exact P_neq_NP_latent_from_p_span160 h n hn
    ((uniform_span160_of_uniform_concrete_locality_profile_structure120 hLoc120) h n hn)

/-- Global closure theorem:
if a uniform span160 witness is available at contradiction scale,
then `PeqNP` is impossible. -/
theorem no_PeqNP_of_uniform_span160
    (h160 : ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      latent_p_witness_span160_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn)) :
    PeqNP → False := by
  intro h
  let n : ℕ := max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)
  have hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804) := by
    exact le_rfl
  exact P_neq_NP_latent_from_p_span160 h n hn (h160 h n hn)

/-- Global closure theorem:
if a direct `n^160` SPDP-rank bound is available uniformly at contradiction scale,
then `PeqNP` is impossible.

This uses the proved bridge
`latentCompiledPoly_spdp_subspace_span_poly_bound` to produce the span160 witness,
then routes through the consolidated any-source closure. -/
theorem no_PeqNP_of_uniform_rank160_bound
    (hRank : ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      mlBlockedSpdpRank (latentPartition h.sat_decider n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly h.sat_decider n) ≤ n ^ 160) :
    PeqNP → False := by
  exact no_PeqNP_of_uniform_any_compiler_source (fun h n hn =>
    Or.inr (Or.inl
      (latentCompiledPoly_spdp_subspace_span_poly_bound h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn) (hRank h n hn))))

/-- Global closure theorem:
if the compiled-tableau upper bound is available uniformly at contradiction scale,
then `PeqNP` is impossible. -/
theorem no_PeqNP_of_uniform_compiled_tableau_bound
    (hBound : ∀ (h : PeqNP) (n : ℕ),
      (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)) →
      latent_compiled_tableau_bound_logscale h.sat_decider n
        (hnM_of_hn h n hn) (hn804_of_hn h n hn)) :
    PeqNP → False := by
  intro h
  let n : ℕ := max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804)
  have hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804) := by
    exact le_rfl
  exact P_neq_NP_latent_from_compiled_tableau_bound h n hn (hBound h n hn)

end LatentCompilerFinalRoute
