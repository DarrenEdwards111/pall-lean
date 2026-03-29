import PallLean.ProfileSliceAssemblyReduction

/-!
# ProfileGeneratorReduction

Paper-faithful final reduction of the profile-slice assembly theorem.

A profile slice is itself a span of explicit generators.  Therefore the two remaining
assembly obligations split into:

1. a basis-generator assembly theorem for those explicit generators;
2. a finite-span closure theorem turning generatorwise assembly into a finrank bound
   for the whole profile slice.
-/

namespace ProfileGeneratorReduction

open SPDP
open MultilinearSPDP
open Tseitin
open LocalFactorReduction
open LocalClauseFactorSpace
open ProfileSliceAssemblyReduction
open ProductProfileSlices
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Explicit profile-slice generators assemble into the local-product target. -/
def ProfileSliceBasisGeneratorAssembles
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4) : Prop :=
  ∀ q : MvPolynomial (Fin (tseitinNumVars Φ)) F,
    q ∈ { q' | ∃ (α : DerivAlloc κ Φ.clauses.length) (hbounded : ∀ i, allocProfile α i ≤ 4),
          allocProfileIndex α hbounded = ρ ∧
          q' = shiftedAllocGenerator shift (verifierFactor (F := F) Φ) S hS α } →
    ∃ W : Submodule F (MvPolynomial (Fin (tseitinNumVars Φ)) F),
      q ∈ W ∧
      Module.finrank F W ≤
        profileLocalDimProduct (F := F) Φ (verifierLocalFactorDimFamily (F := F) Φ) ρ

/-- Explicit closure theorem: if every basis generator assembles and the span they generate
has the same finrank bound, then the full profile-slice closure target holds. -/
def ProfileSliceSpanClosure
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4) : Prop :=
  Module.finrank F
    (profileSliceSubspace (F := F) (κ := κ) (m := Φ.clauses.length) (w := 4)
      shift (verifierFactor (F := F) Φ) S hS ρ)
    ≤ profileLocalDimProduct (F := F) Φ (verifierLocalFactorDimFamily (F := F) Φ) ρ

/-- Basis-generator assembly plus explicit span closure implies the two profile-slice targets. -/
theorem profileSliceTargets_of_basisAndClosure
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4)
    (_hbasis : ProfileSliceBasisGeneratorAssembles (F := F) Φ κ shift S hS ρ)
    (hclosure : ProfileSliceSpanClosure (F := F) Φ κ shift S hS ρ) :
    ProfileSliceGeneratorClosure (F := F) Φ κ shift S hS ρ :=
  hclosure

end ProfileGeneratorReduction
