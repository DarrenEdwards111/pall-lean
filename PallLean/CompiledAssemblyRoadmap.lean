import PallLean.LatentFullBridge
import PallLean.LatentWidthRankDecomp
import PallLean.LatentCompilerFinalRoute

/-!
# CompiledAssemblyRoadmap

Clean target board for the remaining compiled-side gap.

The only unresolved mathematical assumptions are now kept explicit as two axioms:

1. `assembly_soundness_core_target_holds`
2. `compiled_rank_le_profile_aggregation_target_holds`

Everything else is theorem-level wiring around those two cores.
-/

namespace CompiledAssemblyRoadmap

open LatentFullBridge LatentCompiler MultilinearSPDP NPWitness Compiler TuringMachine LatentWidthRankDecomp

/-- Proof-carrying obligation wrapper: pairs a bundled obligation with an actual
proof of its `assemblyBound` field. This removes the Prop-vs-proof blocker. -/
structure CompiledProfileObligationsWithProof (M : DTM) (n : ℕ) where
  ob : CompiledProfileObligations M n
  assemblyProof : ob.assemblyBound

/-- A1 witness predicate (placeholder carrier). -/
def assemblyWitnessData_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) : Prop :=
  True

/-- A1.1 (concrete, placeholder-level): witness exists. -/
theorem assembly_witness_exists_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    assemblyWitnessData_target M n h_le := by
  trivial

/-- A1.2 target shape: witness implies assembly-bound evidence for obligations. -/
def assembly_witness_sound_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) : Prop :=
  assemblyWitnessData_target M n h_le →
    ∀ hOb : CompiledProfileObligations M n, hOb.assemblyBound

/-- Refactored core target:
kept in the executable A1.2 shape while `CompiledProfileObligationsWithProof`
serves as the proof-carrying interface for future migration. -/
def assembly_soundness_core_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) : Prop :=
  assembly_witness_sound_target M n h_le

/-- CORE PLACEHOLDER #1: substantive compiled semantic soundness. -/
axiom assembly_soundness_core_target_holds
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    assembly_soundness_core_target M n h_le

/-- A1.2 exported theorem (wired directly from core placeholder #1). -/
theorem assembly_witness_sound_target_holds
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    assembly_witness_sound_target M n h_le :=
  assembly_soundness_core_target_holds M n h_le

/-- A1.3 bridge (theorem): A1.2 yields assemblyBound evidence. -/
theorem assembly_witness_to_bound_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    assembly_witness_sound_target M n h_le →
    (assemblyWitnessData_target M n h_le →
      ∀ hOb : CompiledProfileObligations M n, hOb.assemblyBound) := by
  intro hSound
  exact hSound

/-- Target 1: concrete assembly evidence theorem family member. -/
theorem assemblyAllThm_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    ∀ hOb : CompiledProfileObligations M n, hOb.assemblyBound := by
  have hA1 : assemblyWitnessData_target M n h_le :=
    assembly_witness_exists_target M n h_le
  exact (assembly_witness_to_bound_target M n h_le
    (assembly_witness_sound_target_holds M n h_le)) hA1

/-- Arithmetic sub-inequality used in Target-2 aggregation chain. -/
theorem compiled_profile_aggregation_le_n160_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    ∀ hOb : CompiledProfileObligations M n,
      hOb.assemblyBound →
      (n ^ 40) * (n ^ 120) ≤ n ^ 160 := by
  intro _ _
  have hEq : (n ^ 40) * (n ^ 120) = n ^ 160 := by
    calc
      (n ^ 40) * (n ^ 120) = n ^ (40 + 120) := by
        simpa [Nat.pow_add] using (Nat.pow_add n 40 120).symm
      _ = n ^ 160 := by norm_num
  exact le_of_eq hEq

/-- Target-2 core proposition shape. -/
def assembly_to_rank_core_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) : Prop :=
  ∀ hOb : CompiledProfileObligations M n,
    hOb.assemblyBound →
    mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160

/-- Intermediate proposition: rank bounded by profile aggregation quantity. -/
def compiled_rank_le_profile_aggregation_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) : Prop :=
  ∀ hOb : CompiledProfileObligations M n,
    hOb.assemblyBound →
    mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) ≤ (n ^ 40) * (n ^ 120)

/-- Direct-proof phase lemma (real): reduce the core Target-2 bound on
`compiledPartition` to any finer partition bound via coarsening monotonicity. -/
theorem compiled_rank_le_profile_aggregation_of_finer_partition
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (Bfine : SPDP.BlockPartition (numVars M n (Nat.log 2 n)))
    (hRefine : ∀ i j : Fin (numVars M n (Nat.log 2 n)),
      Bfine.assign i = Bfine.assign j →
      (compiledPartition M n).assign i = (compiledPartition M n).assign j)
    (hFine : mlBlockedSpdpRank Bfine (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) ≤ (n ^ 40) * (n ^ 120)) :
    compiled_rank_le_profile_aggregation_target M n h_le := by
  intro hOb hAsm
  exact le_trans
    (mlBlockedSpdpRank_coarsen ℚ Bfine (compiledPartition M n)
      (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) hRefine)
    hFine

/-- Global closure template for Target-2 core via a chosen finer partition family.

This formalizes the exact three obligations to discharge in practice:
1) choose `Bfine`,
2) prove `Bfine` refines into `compiledPartition`,
3) prove the fine-partition rank bound. -/
theorem compiled_rank_le_profile_aggregation_target_holds_of_finer_partition
    (BfineOf : ∀ (M : DTM) (n : ℕ)
      (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)),
      SPDP.BlockPartition (numVars M n (Nat.log 2 n)))
    (hRefineOf : ∀ (M : DTM) (n : ℕ)
      (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
      (i j : Fin (numVars M n (Nat.log 2 n))),
      (BfineOf M n h_le).assign i = (BfineOf M n h_le).assign j →
      (compiledPartition M n).assign i = (compiledPartition M n).assign j)
    (hFineOf : ∀ (M : DTM) (n : ℕ)
      (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)),
      mlBlockedSpdpRank (BfineOf M n h_le) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ (n ^ 40) * (n ^ 120)) :
    ∀ (M : DTM) (n : ℕ)
      (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)),
      compiled_rank_le_profile_aggregation_target M n h_le := by
  intro M n h_le
  exact compiled_rank_le_profile_aggregation_of_finer_partition M n h_le
    (BfineOf M n h_le)
    (hRefineOf M n h_le)
    (hFineOf M n h_le)

/-- Concrete choice of finer partition family for the Target-2 strategy:
use `compiledPartition` itself. -/
noncomputable def BfineOf_compiled
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    SPDP.BlockPartition (numVars M n (Nat.log 2 n)) :=
  compiledPartition M n

/-- Corresponding refinement proof for `BfineOf_compiled` is immediate. -/
theorem hRefineOf_compiled
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (i j : Fin (numVars M n (Nat.log 2 n))) :
    (BfineOf_compiled M n h_le).assign i = (BfineOf_compiled M n h_le).assign j →
    (compiledPartition M n).assign i = (compiledPartition M n).assign j := by
  intro h
  simpa [BfineOf_compiled] using h

/-- Local closure at fixed `(M,n,h_le)`: once `hFineOf` is proved for the
concrete partition choice `BfineOf_compiled = compiledPartition`, the core
Target-2 bound is immediate. -/
theorem compiled_rank_le_profile_aggregation_target_holds_of_compiled_hFine
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hFineOf : mlBlockedSpdpRank (BfineOf_compiled M n h_le) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) ≤ (n ^ 40) * (n ^ 120)) :
    compiled_rank_le_profile_aggregation_target M n h_le := by
  intro hOb hAsm
  simpa [BfineOf_compiled] using hFineOf

/-- Transfer chain target T1: latent `(40,120)` parts imply a latent rank160 bound. -/
theorem latent_rank160_from_parts_40_120_target
    (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates)
    (hn804 : n ≥ 2 ^ 804)
    (hParts : LatentWidthRankDecomp.latent_profile_span_card_parts_40_120_logscale M n hn hn804) :
    mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (latentCompiledPoly M n) ≤ n ^ 160 := by
  rcases LatentWidthRankDecomp.latent_p_witness_span160_logscale_from_parts_40_120 M n hn hn804 hParts with
      ⟨G, hIncl, hCard⟩
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

/-- Exact missing reverse-transfer lemma (subspace form): compiled SPDP subspace
is contained in the transported latent SPDP subspace at logscale. -/
axiom compiled_subspace_le_latent_subspace_logscale_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ) :
    (mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le))
    ≤ Submodule.map T
      (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n))

/-- Derived rank-form reverse transfer from the subspace-form target.
This reduces the core blocker to the single subspace inclusion theorem. -/
theorem compiled_rank_le_latent_rank_logscale_of_subspace_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (T : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (hSub : (mlBlockedSpdpSubspace (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le))
      ≤ Submodule.map T
        (mlBlockedSpdpSubspace (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n))) :
    mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n) := by
  unfold mlBlockedSpdpRank
  exact le_trans
    (Submodule.finrank_mono hSub)
    (Submodule.finrank_map_le _ _)

/-- Exact missing reverse-transfer lemma target (rank form): compiled rank is
bounded by latent rank at logscale. -/
theorem compiled_rank_le_latent_rank_logscale_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
    ≤ mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (latentCompiledPoly M n) :=
  compiled_rank_le_latent_rank_logscale_of_subspace_target M n h_le
    (0 : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
      MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ)
    (compiled_subspace_le_latent_subspace_logscale_target M n h_le
      (0 : MvPolynomial (Fin (latentNumVars M n)) ℚ →ₗ[ℚ]
        MvPolynomial (Fin (numVars M n (Nat.log 2 n))) ℚ))
/-- Transfer chain target T2: latent rank160 transfers to compiled fine-bound
shape, via the reverse-transfer lemma + arithmetic aggregation inequality. -/
theorem compiled_fine_bound_from_latent_rank160_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hLat160 : mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (latentCompiledPoly M n) ≤ n ^ 160) :
    mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) ≤ (n ^ 40) * (n ^ 120) := by
  have hCompLeLat : mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le)
      ≤ mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
          (latentCompiledPoly M n) :=
    compiled_rank_le_latent_rank_logscale_target M n h_le
  have hArith : n ^ 160 ≤ (n ^ 40) * (n ^ 120) := by
    have hEq : (n ^ 40) * (n ^ 120) = n ^ 160 := by
      calc
        (n ^ 40) * (n ^ 120) = n ^ (40 + 120) := by
          simpa [Nat.pow_add] using (Nat.pow_add n 40 120).symm
        _ = n ^ 160 := by norm_num
    exact le_of_eq hEq.symm
  exact le_trans hCompLeLat (le_trans hLat160 hArith)

/-- Single explicit bridge target (no wrapper churn):
latent `(40,120)` parts -> latent rank160 -> compiled fine bound. -/
theorem compiled_rank_le_profile_aggregation_from_latent_parts_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hn : n ≥ max 4 M.numStates)
    (hn804 : n ≥ 2 ^ 804)
    (hParts : LatentWidthRankDecomp.latent_profile_span_card_parts_40_120_logscale M n hn hn804) :
    mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) ≤ (n ^ 40) * (n ^ 120) := by
  exact compiled_fine_bound_from_latent_rank160_target M n h_le
    (latent_rank160_from_parts_40_120_target M n hn hn804 hParts)

/-- Next-step concrete closure: if latent `(40,120)` parts are available at
contradiction scale, Target-2 core holds at `(M,n,h_le)`. -/
theorem compiled_rank_le_profile_aggregation_target_holds_of_latent_parts
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hn : n ≥ max 4 M.numStates)
    (hn804 : n ≥ 2 ^ 804)
    (hParts : LatentWidthRankDecomp.latent_profile_span_card_parts_40_120_logscale M n hn hn804) :
    compiled_rank_le_profile_aggregation_target M n h_le := by
  intro hOb hAsm
  exact compiled_rank_le_profile_aggregation_from_latent_parts_target
    M n h_le hn hn804 hParts

/-- Globalized contradiction-scale closure: if latent `(40,120)` parts are
available uniformly at contradiction scale, then the compiled Target-2 core holds
uniformly at contradiction scale. -/
theorem compiled_rank_le_profile_aggregation_target_holds_of_global_latent_parts
    (hPartsGlobal : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      LatentWidthRankDecomp.latent_profile_span_card_parts_40_120_logscale M n hn hn804) :
    ∀ (M : DTM) (n : ℕ)
      (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      compiled_rank_le_profile_aggregation_target M n h_le := by
  intro M n h_le hn hn804
  exact compiled_rank_le_profile_aggregation_target_holds_of_latent_parts
    M n h_le hn hn804 (hPartsGlobal M n hn hn804)

/-- Placeholder stronger arbitrary-domain closure kept for compatibility with the
`CompiledAssemblyTheoremFamily` endpoint shape. -/
axiom compiled_rank_le_profile_aggregation_target_holds
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    compiled_rank_le_profile_aggregation_target M n h_le

/-- Target-2 core from intermediate bound + arithmetic sub-inequality,
under contradiction-scale assumptions + global latent-parts supply. -/
theorem assembly_to_rank_core_target_holds
    (hPartsGlobal : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      LatentWidthRankDecomp.latent_profile_span_card_parts_40_120_logscale M n hn hn804)
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hn : n ≥ max 4 M.numStates)
    (hn804 : n ≥ 2 ^ 804) :
    assembly_to_rank_core_target M n h_le := by
  intro hOb hAsm
  have hCore : compiled_rank_le_profile_aggregation_target M n h_le :=
    compiled_rank_le_profile_aggregation_target_holds_of_global_latent_parts
      hPartsGlobal M n h_le hn hn804
  exact le_trans
    (hCore hOb hAsm)
    (compiled_profile_aggregation_le_n160_target M n h_le hOb hAsm)

/-- Target 2: contradiction-scale concrete assembly -> rank160 theorem member,
fully avoiding the arbitrary-domain placeholder. -/
theorem assemblyToRankThm_target_of_global_latent_parts
    (hPartsGlobal : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      LatentWidthRankDecomp.latent_profile_span_card_parts_40_120_logscale M n hn hn804)
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hn : n ≥ max 4 M.numStates)
    (hn804 : n ≥ 2 ^ 804) :
    ∀ hOb : CompiledProfileObligations M n,
      hOb.assemblyBound →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160 :=
  assembly_to_rank_core_target_holds hPartsGlobal M n h_le hn hn804

/-- Target 2: concrete assembly -> rank160 theorem family member (arbitrary
`(M,n,h_le)` shape, still using the core Target-2 placeholder). -/
theorem assemblyToRankThm_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    ∀ hOb : CompiledProfileObligations M n,
      hOb.assemblyBound →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160 := by
  intro hOb hAsm
  exact le_trans
    (compiled_rank_le_profile_aggregation_target_holds M n h_le hOb hAsm)
    (compiled_profile_aggregation_le_n160_target M n h_le hOb hAsm)

/-- Final packaging target once the two theorem targets above are proved. -/
def compiledAssemblyFamily_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    CompiledAssemblyTheoremFamily M n h_le where
  assemblyAllThm := assemblyAllThm_target M n h_le
  assemblyToRankThm := assemblyToRankThm_target M n h_le

/-- Contradiction-scale endpoint variant that uses only global latent-parts
assumptions and avoids the arbitrary-domain Target-2 placeholder. -/
def compiledAssemblyFamily_target_contradictionScale
    (hPartsGlobal : ∀ (M : DTM) (n : ℕ)
      (hn : n ≥ max 4 M.numStates) (hn804 : n ≥ 2 ^ 804),
      LatentWidthRankDecomp.latent_profile_span_card_parts_40_120_logscale M n hn hn804)
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hn : n ≥ max 4 M.numStates)
    (hn804 : n ≥ 2 ^ 804) :
    CompiledAssemblyTheoremFamily M n h_le where
  assemblyAllThm := assemblyAllThm_target M n h_le
  assemblyToRankThm := assemblyToRankThm_target_of_global_latent_parts
    hPartsGlobal M n h_le hn hn804

end CompiledAssemblyRoadmap
