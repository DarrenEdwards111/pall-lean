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

No assumptions are hidden here; this file is a proof-work target board.
-/

namespace CompiledAssemblyRoadmap

open LatentFullBridge LatentCompiler MultilinearSPDP NPWitness Compiler TuringMachine

/-- Target 1: concrete compiled assembly evidence for each obligation instance. -/
theorem assemblyAllThm_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    ∀ hOb : CompiledProfileObligations M n, hOb.assemblyBound := by
  -- TODO: prove from compiled assembly construction lemmas.
  sorry

/-- Target 2: concrete compiled assembly -> rank160 implication. -/
theorem assemblyToRankThm_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    ∀ hOb : CompiledProfileObligations M n,
      hOb.assemblyBound →
      mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
        (fullCompiledPoly ℚ M n h_le) ≤ n ^ 160 := by
  -- TODO: prove via profile-count + within-profile + assembly aggregation.
  sorry

/-- Final packaging target once the two theorem targets above are proved. -/
def compiledAssemblyFamily_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    CompiledAssemblyTheoremFamily M n h_le where
  assemblyAllThm := assemblyAllThm_target M n h_le
  assemblyToRankThm := assemblyToRankThm_target M n h_le

end CompiledAssemblyRoadmap
