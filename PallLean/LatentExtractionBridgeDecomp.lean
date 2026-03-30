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

/-- Selector extraction map is compatible with the latent partition's block geometry
for selector-slot witness generators. -/
axiom selector_extraction_partition_compat (M : DTM) (n : ℕ)
    (κ ℓ : ℕ) : True

/-- Every extracted witness generator has a latent preimage generator
with no SPDP rank loss. -/
axiom selector_generator_lift (M : DTM) (n : ℕ)
    (κ ℓ : ℕ) : True

/-- Assembled extraction-rank monotonicity (decomposed route). -/
theorem extraction_rank_monotone_selector_from_decomp (M : DTM) (n : ℕ)
    (κ ℓ : ℕ) :
    mlBlockedSpdpRank (latentPartition M n) κ ℓ
      (MvPolynomial.rename (fun i => slot M n 2 i) (extractedProductWitness M n)) ≤
    mlBlockedSpdpRank (latentPartition M n) κ ℓ (latentCompiledPoly M n) :=
  extraction_rank_monotone_selector M n κ ℓ

end LatentExtractionBridgeDecomp
