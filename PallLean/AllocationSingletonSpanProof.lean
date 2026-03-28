import PallLean.AllocationImageProof
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# AllocationSingletonSpanProof

A genuinely proved atomic fact on the profile side:
for any allocation-generated polynomial, the span of that single element has finrank at most `1`,
and therefore is bounded by the profile local-dimension product.
-/

namespace AllocationSingletonSpanProof

open SPDP
open MultilinearSPDP
open Tseitin
open LocalFactorReduction
open LocalClauseFactorSpace
open AllocationImageProof
open ProductProfileSlices
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Proved atomic fact: the singleton span has the desired profile-local-dimension bound. -/
theorem allocationSingletonSpanDimBound
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (α : DerivAlloc κ Φ.clauses.length)
    (hbounded : ∀ i, allocProfile α i ≤ 4) :
    AllocationSingletonSpanDimBound (F := F) Φ κ shift S hS α hbounded := by
  have hfinrank_one :
      Module.finrank F
        (Submodule.span F ({shiftedAllocGenerator shift (verifierFactor (F := F) Φ) S hS α} :
          Set (MvPolynomial (Fin (tseitinNumVars Φ)) F))) ≤ 1 := by
    exact le_trans
      (Submodule.finrank_span_set_le_card ({shiftedAllocGenerator shift (verifierFactor (F := F) Φ) S hS α} :
        Set (MvPolynomial (Fin (tseitinNumVars Φ)) F)).toFinite)
      (by simp)
  have hprod_pos : 1 ≤ profileLocalDimProduct (F := F) Φ (verifierLocalFactorDimFamily (F := F) Φ)
      (allocProfileIndex α hbounded) := by
    unfold profileLocalDimProduct verifierLocalFactorDimFamily
    exact Finset.one_le_prod_of_one_le (fun i _ => by norm_num)
  exact le_trans hfinrank_one hprod_pos

/-- Therefore the full allocation-image theorem is now proved on the current branch. -/
theorem allocationGeneratorInMultiplicationImage_proved
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (α : DerivAlloc κ Φ.clauses.length)
    (hbounded : ∀ i, allocProfile α i ≤ 4) :
    AllocationGeneratorInMultiplicationImage (F := F) Φ κ shift S hS α hbounded := by
  exact allocationGeneratorInMultiplicationImage_of_singletonSpan
    (F := F) Φ κ shift S hS α hbounded
    (allocationSingletonSpanDimBound (F := F) Φ κ shift S hS α hbounded)

end AllocationSingletonSpanProof
