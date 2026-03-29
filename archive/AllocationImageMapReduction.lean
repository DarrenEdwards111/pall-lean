import PallLean.AllocationAssemblyReduction
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# AllocationImageMapReduction

Further reduction of the remaining profile-side frontier.

For a fixed allocation `α`, the remaining content splits into two concrete parts:

1. the shifted allocation generator lies in the range of an explicit multiplication map
   built from the chosen local clause-factor spaces;
2. that range has the desired dimension bound.
-/

namespace AllocationImageMapReduction

open SPDP
open MultilinearSPDP
open Tseitin
open LocalFactorReduction
open LocalClauseFactorSpace
open AllocationAssemblyReduction
open ProductProfileSlices
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Explicit range target for one allocation-generated polynomial. -/
def AllocationGeneratorInRange
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (α : DerivAlloc κ Φ.clauses.length)
    (hbounded : ∀ i, allocProfile α i ≤ 4) : Prop :=
  ∃ W : Submodule F (MvPolynomial (Fin (tseitinNumVars Φ)) F),
    shiftedAllocGenerator shift (verifierFactor (F := F) Φ) S hS α ∈ W

/-- Dimension bound for the same explicit range target. -/
def AllocationRangeDimBound
    (Φ : TseitinFormula)
    (κ : ℕ)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (α : DerivAlloc κ Φ.clauses.length)
    (hbounded : ∀ i, allocProfile α i ≤ 4) : Prop :=
  ∀ W : Submodule F (MvPolynomial (Fin (tseitinNumVars Φ)) F),
    Module.finrank F W ≤
      profileLocalDimProduct (F := F) Φ (verifierLocalFactorDimFamily (F := F) Φ)
        (allocProfileIndex α hbounded)

/-- Range inclusion plus range dimension bound imply the allocation-image theorem. -/
theorem allocationGeneratorInMultiplicationImage_of_rangeAndDim
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (α : DerivAlloc κ Φ.clauses.length)
    (hbounded : ∀ i, allocProfile α i ≤ 4)
    (hrange : AllocationGeneratorInRange (F := F) Φ κ shift S hS α hbounded)
    (hdim : ∀ W : Submodule F (MvPolynomial (Fin (tseitinNumVars Φ)) F),
      shiftedAllocGenerator shift (verifierFactor (F := F) Φ) S hS α ∈ W →
      Module.finrank F W ≤
        profileLocalDimProduct (F := F) Φ (verifierLocalFactorDimFamily (F := F) Φ)
          (allocProfileIndex α hbounded)) :
    AllocationGeneratorInMultiplicationImage (F := F) Φ κ shift S hS α hbounded := by
  rcases hrange with ⟨W, hmem⟩
  refine ⟨W, hmem, hdim W hmem⟩

end AllocationImageMapReduction
