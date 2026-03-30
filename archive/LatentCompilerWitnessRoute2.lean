import PallLean.LatentCompilerWitnessGadgets
import Mathlib.Tactic

/-!
# LatentCompilerWitnessRoute2

This file turns the improved latent extraction into an explicit witness route.

The key new fact from `LatentCompilerWitnessGadgets` is that the corrected latent
object extracts to a concrete base-space polynomial

  2 + ∏ i, (1 - X_i).

So the remaining NP-side work is no longer vague. It splits into two precise tasks:

1. show the extracted base-space product witness has large SPDP rank;
2. show extraction from the latent object is rank-monotone.

Once those are proved, the old monolithic `latent_extracts_hard_witness` theorem can be
replaced by a genuine theorem.
-/

namespace LatentCompilerWitnessRoute2

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open LatentCompilerRoute
open LatentCompilerWitnessGadgets

/-- The explicit base-space witness polynomial revealed by the corrected latent extractor. -/
noncomputable def extractedProductWitness (M : DTM) (n : ℕ) :
    MvPolynomial (Fin (latentBaseVars M n)) ℚ :=
  ∏ i : Fin (latentBaseVars M n), (1 - X i : MvPolynomial (Fin (latentBaseVars M n)) ℚ)

/-- The corrected latent object extracts to `2 + extractedProductWitness`. -/
theorem latentCompiledPolyW_extracts_to_product (M : DTM) (n : ℕ) :
    extractSelectorLayer M n (latentCompiledPolyW M n) =
      (2 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) + extractedProductWitness M n := by
  simpa [extractedProductWitness] using extractSelectorLayer_latentCompiledPolyW M n

/-- NP-side remaining task A:
prove the explicit extracted product witness has large SPDP rank. -/
axiom extractedProductWitness_rank_lower (M : DTM) (n : ℕ)
    (κ : ℕ) (hκ : κ ≥ 5) :
    n ^ (κ / 4) ≤
      mlBlockedSpdpRank (compiledPartition M n) κ κ (extractedProductWitness M n)

/-- NP-side remaining task B:
extraction to the selector layer is rank-monotone for the corrected latent object. -/
axiom latent_selector_extraction_monotone (M : DTM) (n : ℕ)
    (κ ℓ : ℕ) :
    ∀ p : MvPolynomial (LatentVar M n) ℚ,
      mlBlockedSpdpRank (compiledPartition M n) κ ℓ (extractSelectorLayer M n p) ≤
      mlBlockedSpdpRank (latentPartition M n) κ ℓ p

/-- If the two explicit NP-side tasks are solved, the latent hard-witness theorem follows. -/
theorem latent_extracts_hard_witness_from_product
    (M : DTM) (n : ℕ)
    (κ : ℕ) (hκ : κ ≥ 5)
    (hconst : mlBlockedSpdpRank (compiledPartition M n) κ κ
      ((2 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) + extractedProductWitness M n) =
      mlBlockedSpdpRank (compiledPartition M n) κ κ (extractedProductWitness M n)) :
    n ^ (κ / 4) ≤ mlBlockedSpdpRank (latentPartition M n) κ κ (latentCompiledPolyW M n) := by
  have hlow : n ^ (κ / 4) ≤
      mlBlockedSpdpRank (compiledPartition M n) κ κ
        ((2 : MvPolynomial (Fin (latentBaseVars M n)) ℚ) + extractedProductWitness M n) := by
    rw [hconst]
    exact extractedProductWitness_rank_lower M n κ hκ
  have hextract :
      mlBlockedSpdpRank (compiledPartition M n) κ κ
        (extractSelectorLayer M n (latentCompiledPolyW M n)) ≤
      mlBlockedSpdpRank (latentPartition M n) κ κ (latentCompiledPolyW M n) :=
    latent_selector_extraction_monotone M n κ κ (latentCompiledPolyW M n)
  rw [latentCompiledPolyW_extracts_to_product M n] at hextract
  exact le_trans hlow hextract

end LatentCompilerWitnessRoute2
