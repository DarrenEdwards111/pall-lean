import PallLean.ProfileBasisFactorizationReduction

/-!
# AllocationAssemblyReduction

Final atomic reduction on the profile-assembly side.

For a fixed derivative allocation `α`, the shifted allocation generator is literally a product of
one local derivative contribution from each clause factor, followed by multilinear projection and
multiplication by the common shift. So the remaining content is to show this concrete product lands
in a finite-dimensional multiplication-image space built from the local clause-factor spaces.
-/

namespace AllocationAssemblyReduction

open SPDP
open MultilinearSPDP
open Tseitin
open LocalFactorReduction
open LocalClauseFactorSpace
open ProfileBasisFactorizationReduction
open ProductProfileSlices
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Explicit multiplication-image theorem for one allocation-generated polynomial. -/
def AllocationGeneratorInMultiplicationImage
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (α : DerivAlloc κ Φ.clauses.length)
    (hbounded : ∀ i, allocProfile α i ≤ 4) : Prop :=
  ∃ W : Submodule F (MvPolynomial (Fin (tseitinNumVars Φ)) F),
    shiftedAllocGenerator shift (verifierFactor (F := F) Φ) S hS α ∈ W ∧
    Module.finrank F W ≤
      profileLocalDimProduct (F := F) Φ (verifierLocalFactorDimFamily (F := F) Φ)
        (allocProfileIndex α hbounded)

/-- The explicit multiplication-image theorem is exactly the remaining allocation factorization target. -/
theorem allocationGeneratorFactorsThroughLocalSpaces_of_image
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (α : DerivAlloc κ Φ.clauses.length)
    (hbounded : ∀ i, allocProfile α i ≤ 4)
    (himg : AllocationGeneratorInMultiplicationImage (F := F) Φ κ shift S hS α hbounded) :
    AllocationGeneratorFactorsThroughLocalSpaces (F := F) Φ κ shift S hS α hbounded :=
  himg

end AllocationAssemblyReduction
