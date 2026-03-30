import PallLean.LatentCompiler
import Mathlib.Tactic

/-!
# LatentExtractionBridgeDecomp

Decomposes the remaining NP-side bridge axiom
`extraction_rank_monotone_selector` into paper-shaped sub-obligations.

Idea:
1) identify a selector-visible extracted witness subspace;
2) show that subspace embeds into the latent SPDP subspace.
-/

namespace LatentExtractionBridgeDecomp

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open LatentCompiler

/-- Selector-slot derivative lists are block-admissible under latentPartition. -/
theorem selector_extraction_partition_compat (M : DTM) (n : ℕ)
    (S : List (Fin (latentBaseVars M n))) (hnd : S.Nodup) :
    isBlockAdmissible (latentPartition M n) (S.map (selSlot M n)) :=
  selSlotList_admissible M n S hnd

/-- The extracted product witness lifts back to the selector layer by rename. -/
theorem selector_generator_lift (M : DTM) (n : ℕ) :
    MvPolynomial.rename (fun i => slot M n 2 i) (extractedProductWitness M n) =
      ∏ i : Fin (latentBaseVars M n),
        (1 - X (selSlot M n i) : MvPolynomial (Fin (latentNumVars M n)) ℚ) := by
  unfold extractedProductWitness
  simp [slot, selSlot]

/-- Final assembly obligation for extraction monotonicity at the
log-scale parameters used in the contradiction (κ = ℓ = log₂ n). -/
axiom selector_extraction_monotone_assembly_logscale (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804) :
    mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (MvPolynomial.rename (fun i => slot M n 2 i) (extractedProductWitness M n)) ≤
    mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n) (latentCompiledPoly M n)

/-- Assembled extraction-rank monotonicity at contradiction scale.
Uses compatibility + lift prerequisites and discharges with the log-scale
assembly obligation. -/
theorem extraction_rank_monotone_selector_from_decomp (M : DTM) (n : ℕ)
    (hn804 : n ≥ 2 ^ 804) :
    mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n)
      (MvPolynomial.rename (fun i => slot M n 2 i) (extractedProductWitness M n)) ≤
    mlBlockedSpdpRank (latentPartition M n) (Nat.log 2 n) (Nat.log 2 n) (latentCompiledPoly M n) := by
  have _hCompat : isBlockAdmissible (latentPartition M n) (([] : List (Fin (latentBaseVars M n))).map (selSlot M n)) :=
    selector_extraction_partition_compat M n [] List.nodup_nil
  have _hLift : MvPolynomial.rename (fun i => slot M n 2 i) (extractedProductWitness M n) =
      ∏ i : Fin (latentBaseVars M n),
        (1 - X (selSlot M n i) : MvPolynomial (Fin (latentNumVars M n)) ℚ) :=
    selector_generator_lift M n
  exact selector_extraction_monotone_assembly_logscale M n hn804

end LatentExtractionBridgeDecomp
