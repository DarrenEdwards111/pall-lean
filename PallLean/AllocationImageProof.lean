import PallLean.AllocationImageMapReduction
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# AllocationImageProof

A genuinely proved atomic fact on the profile side:
every allocation-generated polynomial lies in a finite-dimensional subspace, namely the
span of itself. This leaves only the singleton-span finrank estimate.
-/

namespace AllocationImageProof

open SPDP
open MultilinearSPDP
open Tseitin
open LocalFactorReduction
open LocalClauseFactorSpace
open AllocationAssemblyReduction
open AllocationImageMapReduction
open ProductProfileSlices
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Proved atomic fact: any allocation generator lies in the span of itself. -/
theorem allocationGeneratorInRange
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (α : DerivAlloc κ Φ.clauses.length)
    (hbounded : ∀ i, allocProfile α i ≤ 4) :
    AllocationGeneratorInRange (F := F) Φ κ shift S hS α hbounded := by
  refine ⟨Submodule.span F ({shiftedAllocGenerator shift (verifierFactor (F := F) Φ) S hS α} :
    Set (MvPolynomial (Fin (tseitinNumVars Φ)) F)), ?_⟩
  exact Submodule.subset_span (by simp)

/-- Remaining atomic profile-side dimension target: the singleton span already has the desired bound. -/
def AllocationSingletonSpanDimBound
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (α : DerivAlloc κ Φ.clauses.length)
    (hbounded : ∀ i, allocProfile α i ≤ 4) : Prop :=
  Module.finrank F
    (Submodule.span F ({shiftedAllocGenerator shift (verifierFactor (F := F) Φ) S hS α} :
      Set (MvPolynomial (Fin (tseitinNumVars Φ)) F)))
    ≤ profileLocalDimProduct (F := F) Φ (verifierLocalFactorDimFamily (F := F) Φ)
        (allocProfileIndex α hbounded)

/-- The singleton-span dimension bound implies the full allocation-image theorem. -/
theorem allocationGeneratorInMultiplicationImage_of_singletonSpan
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (α : DerivAlloc κ Φ.clauses.length)
    (hbounded : ∀ i, allocProfile α i ≤ 4)
    (hsingle : AllocationSingletonSpanDimBound (F := F) Φ κ shift S hS α hbounded) :
    AllocationGeneratorInMultiplicationImage (F := F) Φ κ shift S hS α hbounded := by
  refine ⟨Submodule.span F ({shiftedAllocGenerator shift (verifierFactor (F := F) Φ) S hS α} :
    Set (MvPolynomial (Fin (tseitinNumVars Φ)) F)), ?_, hsingle⟩
  exact Submodule.subset_span (by simp)

end AllocationImageProof
