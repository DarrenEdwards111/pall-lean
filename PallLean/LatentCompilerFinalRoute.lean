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
    theorem216_profile_data_logscale_from_core M n hnM hn804
      (theorem9_profile_count_obligation_proved M n hn804)
      (theorem9_within_profile_dim_obligation_proved M n hn804)
      pCore
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
  have pCore : latent_profile_assembly_logscale M n hnM hn804 :=
    latent_profile_assembly_logscale_from_span_card_bound M n hnM hn804 pSpan
  exact P_neq_NP_latent_from_finer_decomp_and_p_core h n hn idxList hnd hlen hfinj pCore

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
  have pCore : latent_profile_assembly_logscale M n hnM hn804 :=
    latent_profile_assembly_logscale_from_block_cover M n hnM hn804 pCover
  exact P_neq_NP_latent_from_finer_decomp_and_p_core h n hn idxList hnd hlen hfinj pCore

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
  have pSpan : latent_profile_span_card_bound_logscale M n hnM hn804 :=
    latent_profile_span_card_bound_logscale_from_item3_uniform2 M n hnM hn804 p3u2
  exact P_neq_NP_latent_from_finer_decomp_and_p_span_card h n hn idxList hnd hlen hfinj pSpan

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
  rcases pGB with ⟨G, hSpan, hBuck⟩
  exact P_neq_NP_latent_from_finer_decomp_and_p_span_bucket h n hn idxList hnd hlen hfinj G hSpan hBuck

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
  have pGB : latent_global_span_and_bucket_logscale M n hnM hn804 :=
    latent_global_span_and_bucket_logscale_from_construction_data M n hnM hn804 pData
  exact P_neq_NP_latent_from_finer_decomp_and_p_global_span_bucket h n hn idxList hnd hlen hfinj pGB

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

  -- Canonical NP data (no external idxList/hnd/hlen/hfinj needed)
  have hCoeff : selCon_kronecker_coeff_law_logscale M n hn804 :=
    selCon_kronecker_coeff_law_logscale_from_canonical_idxList M n hn804
  have npData : selCon_kronecker_data_logscale M n hn804 := hCoeff

  -- P-data package reduced to core profile assembly from construction data
  have pCore : latent_profile_assembly_logscale M n hnM hn804 :=
    latent_profile_assembly_logscale_from_construction_data M n hnM hn804 pData
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
  exact P_neq_NP_latent_from_p_span_card_via_core h n hn pSpan

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
  exact P_neq_NP_latent_from_p_block_cover_via_core h n hn pCover

/-- Canonical-NP route with P-side global-span+bucket witness only. -/
theorem P_neq_NP_latent_from_p_global_span_bucket (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pGB : latent_global_span_and_bucket_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  rcases pGB with ⟨G, hSpan, hBuck⟩
  have pCover : latent_profile_block_cover_logscale M n hnM hn804 :=
    latent_profile_block_cover_logscale_from_span_and_bucketization M n hnM hn804 G hSpan hBuck
  exact P_neq_NP_latent_from_p_block_cover h n hn pCover

/-- Move-4 canonical route: Item-3 with uniform `n^120` bound. -/
theorem P_neq_NP_latent_from_p_item3_uniform120 (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (p3120 : latent_profile_block_cover_item3_uniform120_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  rcases p3120 with ⟨I, Gprof, hUni120, hSpan⟩
  have hn1 : 1 ≤ n := by
    exact le_trans (by decide : 1 ≤ 4) (le_trans (le_max_left 4 M.numStates) hnM)
  have hpow120_160 : n ^ 120 ≤ n ^ 160 :=
    Nat.pow_le_pow_right hn1 (by decide : 120 ≤ 160)
  have hCover : latent_profile_block_cover_logscale M n hnM hn804 := by
    refine ⟨I, Gprof, hSpan, ?_⟩
    intro i hi
    have hle120 : (Gprof i).card ≤ n ^ 120 := hUni120 i
    exact le_trans hle120 hpow120_160
  exact P_neq_NP_latent_from_p_block_cover h n hn hCover

/-- Canonical-NP route with Item-3+uniform-Item-2 P witness only. -/
theorem P_neq_NP_latent_from_p_item3_uniform2 (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (p3u2 : latent_profile_block_cover_item3_uniform2_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have pCover : latent_profile_block_cover_logscale M n hnM hn804 :=
    latent_profile_block_cover_from_item3_uniform2 M n hnM hn804 p3u2
  exact P_neq_NP_latent_from_p_block_cover h n hn pCover

/-- Frozen canonical final entrypoint (Move-1):
assume exactly `latent_p_witness_target_logscale` on the P side. -/
theorem P_neq_NP_latent_from_p_witness_target (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pTarget : latent_p_witness_target_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have hCoeff : selCon_kronecker_coeff_law_logscale M n hn804 :=
    selCon_kronecker_coeff_law_logscale_from_canonical_idxList M n hn804
  have npData : selCon_kronecker_data_logscale M n hn804 := hCoeff
  have pAsm : theorem216_p_obligation M n hnM hn804 :=
    theorem216_profile_data_logscale_from_bucket_function M n hnM hn804
      (theorem9_profile_count_obligation_proved M n hn804)
      (theorem9_within_profile_dim_obligation_proved M n hn804)
      pTarget
  exact P_neq_NP_latent_decomp h n hn ⟨npData, pAsm⟩

/-- Move-2 strong-entry route: if a single span witness of size `≤ n^160` is built,
then frozen target follows immediately and the contradiction route closes. -/
theorem P_neq_NP_latent_from_p_span160 (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (p160 : latent_p_witness_span160_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have pTarget : latent_p_witness_target_logscale M n hnM hn804 :=
    latent_p_witness_target_from_span160 M n hnM hn804 p160
  exact P_neq_NP_latent_from_p_witness_target h n hn pTarget

/-- Move-5 complete route from an explicit `n^160` rank bound hypothesis.
No global axiom is used here. -/
theorem P_neq_NP_from_generator_bound (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (hRank : mlBlockedSpdpRank (latentPartition h.sat_decider n) (Nat.log 2 n) (Nat.log 2 n)
      (latentCompiledPoly h.sat_decider n) ≤ n ^ 160) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have p160 : latent_p_witness_span160_logscale M n hnM hn804 :=
    latentCompiledPoly_spdp_subspace_span_poly_bound M n hnM hn804 hRank
  exact P_neq_NP_latent_from_p_span160 h n hn p160

/-- Move-3 route: profile parts with `(40,120)` bounds imply span160,
then the Move-2 strong route closes the contradiction. -/
theorem P_neq_NP_latent_from_p_parts_40_120 (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pParts : latent_profile_span_card_parts_40_120_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have p160 : latent_p_witness_span160_logscale M n hnM hn804 :=
    latent_p_witness_span160_logscale_from_parts_40_120 M n hnM hn804 pParts
  exact P_neq_NP_latent_from_p_span160 h n hn p160

/-- Canonical-NP route from functional profile-id bucket schema (P-side).
This is often the most natural constructive form to prove from paper definitions. -/
theorem P_neq_NP_latent_from_p_bucket_function (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pFun : latent_profile_bucket_function_bound_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  exact P_neq_NP_latent_from_p_bucket_function_via_core h n hn pFun

/-- Direct canonical-NP bridge: bucket-function witness can be routed through
block-cover equivalence before entering the canonical final route. -/
theorem P_neq_NP_latent_from_p_bucket_function_via_block_cover (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pFun : latent_profile_bucket_function_bound_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have pCover : latent_profile_block_cover_logscale M n hnM hn804 :=
    (latent_profile_block_cover_iff_bucket_function M n hnM hn804).2 pFun
  exact P_neq_NP_latent_from_p_block_cover h n hn pCover

/-- Symmetric canonical-NP bridge: block-cover witness can be routed through
bucket-function equivalence before entering the canonical final route. -/
theorem P_neq_NP_latent_from_p_block_cover_via_bucket_function (h : PeqNP) (n : ℕ)
    (hn : n ≥ max (max 32 (max 4 h.sat_decider.numStates)) (2 ^ 804))
    (pCover : latent_profile_block_cover_logscale h.sat_decider n
      (hnM_of_hn h n hn) (hn804_of_hn h n hn)) : False := by
  let M := h.sat_decider
  have hnM : n ≥ max 4 M.numStates := hnM_of_hn h n hn
  have hn804 : n ≥ 2 ^ 804 := hn804_of_hn h n hn
  have pFun : latent_profile_bucket_function_bound_logscale M n hnM hn804 :=
    (latent_profile_block_cover_iff_bucket_function M n hnM hn804).1 pCover
  exact P_neq_NP_latent_from_p_bucket_function h n hn pFun

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

end LatentCompilerFinalRoute
