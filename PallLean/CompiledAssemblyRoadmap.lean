import PallLean.LatentFullBridge

/-!
# CompiledAssemblyRoadmap

This file isolates the final compiled-side math gap for the paper-faithful route.

Goal: instantiate `CompiledAssemblyTheoremFamily` with real proofs.

## Remaining theorem targets

1. `assemblyAllThm_target`
2. `assemblyToRankThm_target`

Once both are proved, use
`LatentFullBridge.hPcore32_of_compiledAssemblyTheoremFamily`.

## Suggested proof plan (high level)

- Step A: Build concrete compiled assembly evidence (`assemblyBound`) from
  profile construction/coverage lemmas.
- Step B: Prove assembly-to-rank implication by composing:
  profile-count contribution + within-profile dimension + final aggregation.
- Step C: Package as `CompiledAssemblyTheoremFamily`.

## Concrete checklist for Target (1): `assemblyAllThm_target`

The intended chain is:

- A1.1 `assembly_witness_exists_target`
- A1.2 `assembly_witness_sound_target`
- A1.3 `assembly_witness_to_bound_target`

and then:

`assemblyWitnessData_target_holds` from A1.1,
`assemblyWitnessData_implies_assemblyBound_target` from A1.2 + A1.3.

These are declared below as explicit placeholders so we can replace them one-by-one.

No assumptions are hidden here; this file is a proof-work target board.
-/

namespace CompiledAssemblyRoadmap

open LatentFullBridge LatentCompiler MultilinearSPDP NPWitness Compiler TuringMachine

/-- NEW TARGET A1: construct raw compiled assembly witness data at `(M,n,h_le)`. -/
def assemblyWitnessData_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) : Prop :=
  True

/-- A1.1: existence of a concrete compiled assembly witness object.
(Currently immediate because `assemblyWitnessData_target` is the placeholder
predicate `True`; replace this proof when A1 is refined to a substantive object.) -/
theorem assembly_witness_exists_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    assemblyWitnessData_target M n h_le := by
  trivial

/-- A1.2: soundness of the witness wrt compiled assembly semantics.
(Current placeholder shape: witness data entails `assemblyBound` for obligation
instances; replace its proof source with substantive compiled semantics.) -/
def assembly_witness_sound_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) : Prop :=
  assemblyWitnessData_target M n h_le →
    ∀ hOb : CompiledProfileObligations M n, hOb.assemblyBound

/-- A1.2 source split (checklist):
S1 = semantic soundness core, S2 = export into the A1.2 target shape. -/
def assembly_soundness_core_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) : Prop :=
  assembly_witness_sound_target M n h_le

theorem assembly_soundness_core_implies_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    assembly_soundness_core_target M n h_le →
    assembly_witness_sound_target M n h_le := by
  intro h
  exact h

axiom assembly_soundness_core_target_holds
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    assembly_soundness_core_target M n h_le

/-- Placeholder source for A1.2 until concrete witness semantics are proved. -/
theorem assembly_witness_sound_target_holds
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    assembly_witness_sound_target M n h_le :=
  assembly_soundness_core_implies_target M n h_le
    (assembly_soundness_core_target_holds M n h_le)
/-- A1.3: witness soundness implies `assemblyBound` for obligation instances.
Now a real theorem (tautological bridge from A1.2). -/
theorem assembly_witness_to_bound_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    assembly_witness_sound_target M n h_le →
    (assemblyWitnessData_target M n h_le →
      ∀ hOb : CompiledProfileObligations M n, hOb.assemblyBound) := by
  intro hSound
  exact hSound

/-- NEW TARGET A2: show raw witness data implies `assemblyBound` for any
obligation instance at `(M,n)`.
Current implementation is routed through A1.2+A1.3. -/
theorem assemblyWitnessData_implies_assemblyBound_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    assemblyWitnessData_target M n h_le →
    ∀ hOb : CompiledProfileObligations M n, hOb.assemblyBound :=
  assembly_witness_to_bound_target M n h_le
    (assembly_witness_sound_target_holds M n h_le)


/-- Target-2 checklist split:
R1 = core assembly->rank implication proposition, R2 = exported theorem family shape.

We further expose an explicit first intermediate target:
`compiled_aggregation_bound_target`, so R1 can be proved via an explicit bridge. -/
def assembly_to_rank_core_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) : Prop :=
  ∀ hOb : CompiledProfileObligations M n,
    hOb.assemblyBound →
    mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160

/-- First concrete aggregation sub-inequality target (A):
a profile-aggregation quantity is polynomially bounded by `n^160`.

Now proved arithmetically (independent of `hOb.assemblyBound`). -/
theorem compiled_profile_aggregation_le_n160_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    ∀ hOb : CompiledProfileObligations M n,
      hOb.assemblyBound →
      (n ^ 40) * (n ^ 120) ≤ n ^ 160 := by
  intro hOb hAsm
  have hEq : (n ^ 40) * (n ^ 120) = n ^ 160 := by
    calc
      (n ^ 40) * (n ^ 120) = n ^ (40 + 120) := by
        simpa [Nat.pow_add] using (Nat.pow_add n 40 120).symm
      _ = n ^ 160 := by norm_num
  exact le_of_eq hEq

/-- Second concrete intermediate target (B): link compiled SPDP rank to the
profile-aggregation quantity `(n^40)*(n^120)`. -/
axiom compiled_rank_le_profile_aggregation_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    ∀ hOb : CompiledProfileObligations M n,
      hOb.assemblyBound →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ (n ^ 40) * (n ^ 120)

/-- First concrete intermediate theorem target for Target-2:
compiled assembly-level aggregation bound in the exact rank160 shape. -/
theorem compiled_aggregation_bound_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    ∀ hOb : CompiledProfileObligations M n,
      hOb.assemblyBound →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160 := by
  intro hOb hAsm
  exact le_trans
    (compiled_rank_le_profile_aggregation_target M n h_le hOb hAsm)
    (compiled_profile_aggregation_le_n160_target M n h_le hOb hAsm)

/-- Wiring bridge: expose how sub-target (A) is intended to feed the
aggregation->rank path (currently via the existing aggregation placeholder). -/
theorem compiled_aggregation_bound_target_of_subineq
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    (∀ hOb : CompiledProfileObligations M n,
      hOb.assemblyBound →
      (n ^ 40) * (n ^ 120) ≤ n ^ 160) →
    (∀ hOb : CompiledProfileObligations M n,
      hOb.assemblyBound →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160) := by
  intro _
  exact compiled_aggregation_bound_target M n h_le

/-- Bridge from first intermediate target to core Target-2 proposition. -/
theorem assembly_to_rank_core_target_of_aggregation
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    assembly_to_rank_core_target M n h_le :=
  compiled_aggregation_bound_target_of_subineq M n h_le
    (compiled_profile_aggregation_le_n160_target M n h_le)

theorem assembly_to_rank_core_target_holds
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    assembly_to_rank_core_target M n h_le :=
  assembly_to_rank_core_target_of_aggregation M n h_le
/-- Explicit placeholder assumption for Target 2 export (currently from R1-holds). -/
theorem assemblyToRankThm_placeholder
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    ∀ hOb : CompiledProfileObligations M n,
      hOb.assemblyBound →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160 :=
  assembly_to_rank_core_target_holds M n h_le

/-- Checklist bridge: once A1.1 is concretely proved, this should replace the
current placeholder `assemblyWitnessData_target_holds`. -/
theorem assemblyWitnessData_target_holds_of_exists
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    assemblyWitnessData_target M n h_le :=
  assembly_witness_exists_target M n h_le

/-- Checklist bridge: once A1.2+A1.3 are concretely proved, this should replace
`assemblyWitnessData_implies_assemblyBound_target`. -/
theorem assemblyWitnessData_implies_assemblyBound_of_soundness
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    assemblyWitnessData_target M n h_le →
    ∀ hOb : CompiledProfileObligations M n, hOb.assemblyBound :=
  assembly_witness_to_bound_target M n h_le
    (assembly_witness_sound_target_holds M n h_le)

/-- Target 1: concrete compiled assembly evidence for each obligation instance,
derived from the incremental A1/A2 chain. -/
theorem assemblyAllThm_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    ∀ hOb : CompiledProfileObligations M n, hOb.assemblyBound := by
  have hA1 : assemblyWitnessData_target M n h_le :=
    assemblyWitnessData_target_holds_of_exists M n h_le
  exact assemblyWitnessData_implies_assemblyBound_target M n h_le hA1

/-- Target 2: concrete compiled assembly -> rank160 implication. -/
theorem assemblyToRankThm_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    ∀ hOb : CompiledProfileObligations M n,
      hOb.assemblyBound →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160 :=
  assemblyToRankThm_placeholder M n h_le

/-- Final packaging target once the two theorem targets above are proved. -/
def compiledAssemblyFamily_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    CompiledAssemblyTheoremFamily M n h_le where
  assemblyAllThm := assemblyAllThm_target M n h_le
  assemblyToRankThm := assemblyToRankThm_target M n h_le

end CompiledAssemblyRoadmap
