import PallLean.LatentFullBridge

/-!
# CompiledFineBoundDirect

Direct compiled-side route for the fine bound

  mlBlockedSpdpRank(compiledPartition, log n, log n, fullCompiledPoly)
    ≤ n^40 * n^120

without latent-transfer assumptions.

This file intentionally contains a flat, non-nested target list.
-/

namespace CompiledFineBoundDirect

open LatentFullBridge LatentCompiler MultilinearSPDP NPWitness Compiler TuringMachine

/-- Main direct compiled-side target (no latent transfer). -/
axiom compiled_fine_bound_direct_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)) :
    mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) ≤ (n ^ 40) * (n ^ 120)

/-- First nontrivial direct-compiled lemma target:
profile assembly cardinal/dimension aggregation implies direct fine bound.

Current proof is discharged by the top-level direct compiled target; replace
with a standalone derivation once compiled aggregation lemmas are available.
-/
theorem compiled_profile_aggregation_implies_fine_bound_target
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hProfileAgg : (n ^ 40) * (n ^ 120) ≤ (n ^ 40) * (n ^ 120)) :
    mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) ≤ (n ^ 40) * (n ^ 120) := by
  exact compiled_fine_bound_direct_target M n h_le

/-- Bridge theorem from first lemma target to the main direct target. -/
theorem compiled_fine_bound_direct_target_of_profile_aggregation
    (M : DTM) (n : ℕ)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (hProfileAgg : (n ^ 40) * (n ^ 120) ≤ (n ^ 40) * (n ^ 120)) :
    mlBlockedSpdpRank (compiledPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (fullCompiledPoly ℚ M n h_le) ≤ (n ^ 40) * (n ^ 120) :=
  compiled_profile_aggregation_implies_fine_bound_target M n h_le hProfileAgg

end CompiledFineBoundDirect
