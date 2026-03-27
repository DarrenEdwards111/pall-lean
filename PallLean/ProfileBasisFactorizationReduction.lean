import PallLean.ProfileGeneratorReduction

/-!
# ProfileBasisFactorizationReduction

Further paper-faithful reduction on the profile-assembly side.

A basis generator in a profile slice comes from a concrete derivative allocation `α`.
So the remaining basis-generator assembly theorem reduces to showing that each such
allocation-generated polynomial factors through the chosen local clause-factor spaces.
-/

namespace ProfileBasisFactorizationReduction

open SPDP
open MultilinearSPDP
open Tseitin
open LocalFactorReduction
open LocalClauseFactorSpace
open ProfileGeneratorReduction
open ProductProfileSlices
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Explicit factorization theorem for one allocation-generated basis element. -/
def AllocationGeneratorFactorsThroughLocalSpaces
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

/-- The explicit allocation factorization theorem implies the profile basis-generator assembly theorem. -/
theorem profileSliceBasisGeneratorAssembles_of_allocationFactorization
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4)
    (hfact : ∀ (α : DerivAlloc κ Φ.clauses.length) (hbounded : ∀ i, allocProfile α i ≤ 4),
      allocProfileIndex α hbounded = ρ →
      AllocationGeneratorFactorsThroughLocalSpaces (F := F) Φ κ shift S hS α hbounded) :
    ProfileSliceBasisGeneratorAssembles (F := F) Φ κ shift S hS ρ := by
  intro q hq
  rcases hq with ⟨α, hbounded, hρ, rfl⟩
  simpa [hρ] using hfact α hbounded hρ

end ProfileBasisFactorizationReduction
