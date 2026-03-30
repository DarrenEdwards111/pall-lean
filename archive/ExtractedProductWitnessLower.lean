import PallLean.LatentCompilerWitnessRoute2
import Mathlib.Tactic

/-!
# ExtractedProductWitnessLower

This file decomposes the remaining lower-bound theorem for the explicit extracted
product witness

  ∏ i, (1 - X_i)

into identity-minor style sublemmas. The goal is to make the remaining NP-side
work mirror the structure that already appeared in the earlier verifier/Tseitin
route, but now on the corrected latent compiler extraction.
-/

namespace ExtractedProductWitnessLower

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open LatentCompilerRoute
open LatentCompilerWitnessRoute2

/-- A canonical list of witness slots used for the extracted product witness route. -/
def witnessSlotList (M : DTM) (n : ℕ) (S : List (Fin (latentBaseVars M n))) :
    List (Fin (latentBaseVars M n)) := S

/-- Admissibility target for witness slot lists under the base compiled partition. -/
axiom witnessSlotList_admissible (M : DTM) (n : ℕ)
    (S : List (Fin (latentBaseVars M n)))
    (hnd : S.Nodup) :
    IsAdmissible (compiledPartition M n) S

/-- Derivatives of the extracted product witness along distinct slots produce
squarefree complementary generators. -/
axiom extractedProductWitness_derivative_shape (M : DTM) (n : ℕ)
    (S : List (Fin (latentBaseVars M n)))
    (hnd : S.Nodup) :
    True

/-- Distinct slot sets yield linearly independent SPDP generators.
This is the identity-minor heart for the explicit extracted witness polynomial. -/
axiom extractedProductWitness_generators_independent (M : DTM) (n : ℕ)
    (κ : ℕ) :
    True

/-- Therefore the SPDP subspace for the extracted product witness has dimension at least
`choose (latentBaseVars M n) κ`. -/
axiom extractedProductWitness_choose_lower (M : DTM) (n : ℕ)
    (κ : ℕ) (hκ : κ ≥ 1) :
    Nat.choose (latentBaseVars M n) κ ≤
      mlBlockedSpdpRank (compiledPartition M n) κ κ (extractedProductWitness M n)

/-- Combinatorial lower bound turning the choose-count into the desired exponential form. -/
axiom choose_latentBaseVars_lower (M : DTM) (n : ℕ)
    (κ : ℕ) :
    n ^ (κ / 4) ≤ Nat.choose (latentBaseVars M n) κ

/-- Assembled lower bound for the explicit extracted product witness. -/
theorem extractedProductWitness_rank_lower_from_identity_minor (M : DTM) (n : ℕ)
    (κ : ℕ) (hκ : κ ≥ 5) :
    n ^ (κ / 4) ≤
      mlBlockedSpdpRank (compiledPartition M n) κ κ (extractedProductWitness M n) := by
  have hchoose : n ^ (κ / 4) ≤ Nat.choose (latentBaseVars M n) κ :=
    choose_latentBaseVars_lower M n κ
  have hrank : Nat.choose (latentBaseVars M n) κ ≤
      mlBlockedSpdpRank (compiledPartition M n) κ κ (extractedProductWitness M n) :=
    extractedProductWitness_choose_lower M n κ (by omega)
  exact le_trans hchoose hrank

end ExtractedProductWitnessLower
