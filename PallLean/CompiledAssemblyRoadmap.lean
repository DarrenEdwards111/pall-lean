import PallLean.LatentFullBridge

/-!
# CompiledAssemblyRoadmap

Clean target board for the remaining compiled-side gap.

The only unresolved mathematical assumptions are now kept explicit as two axioms:

1. `assembly_soundness_core_target_holds`
2. `compiled_rank_le_profile_aggregation_target_holds`

Everything else is theorem-level wiring around those two cores.
-/

namespace CompiledAssemblyRoadmap

open LatentFullBridge LatentCompiler MultilinearSPDP NPWitness Compiler TuringMachine

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

/-- CORE PLACEHOLDER #2: substantive compiled rank->aggregation theorem. -/
axiom compiled_rank_le_profile_aggregation_target_holds
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    compiled_rank_le_profile_aggregation_target M n h_le

/-- Target-2 core from intermediate bound + arithmetic sub-inequality. -/
theorem assembly_to_rank_core_target_holds
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    assembly_to_rank_core_target M n h_le := by
  intro hOb hAsm
  exact le_trans
    (compiled_rank_le_profile_aggregation_target_holds M n h_le hOb hAsm)
    (compiled_profile_aggregation_le_n160_target M n h_le hOb hAsm)

/-- Target 2: concrete assembly -> rank160 theorem family member. -/
theorem assemblyToRankThm_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    ∀ hOb : CompiledProfileObligations M n,
      hOb.assemblyBound →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160 :=
  assembly_to_rank_core_target_holds M n h_le

/-- Final packaging target once the two theorem targets above are proved. -/
def compiledAssemblyFamily_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    CompiledAssemblyTheoremFamily M n h_le where
  assemblyAllThm := assemblyAllThm_target M n h_le
  assemblyToRankThm := assemblyToRankThm_target M n h_le

end CompiledAssemblyRoadmap
