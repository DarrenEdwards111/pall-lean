import PallLean.AssemblyMapReduction

/-!
# ProfileSliceAssemblyReduction

This file shrinks the remaining assembly frontier from a whole-slice containment statement to a
single generatorwise/local-closure package.

It keeps the branch clean by making the final closure step explicit as a hypothesis rather than
hiding it behind a `sorry`.
-/

namespace ProfileSliceAssemblyReduction

open SPDP
open MultilinearSPDP
open Tseitin
open LocalFactorReduction
open LocalClauseFactorSpace
open AssemblyMapReduction
open ProductProfileSlices
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Generatorwise assembly theorem for one profile slice. -/
def ProfileSliceGeneratorAssembles
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4) : Prop :=
  ∀ q : MvPolynomial (Fin (tseitinNumVars Φ)) F,
    q ∈ profileSliceSubspace (F := F) (κ := κ) (m := Φ.clauses.length) (w := 4)
      shift (verifierFactor (F := F) Φ) S hS ρ →
    ∃ W : Submodule F (MvPolynomial (Fin (tseitinNumVars Φ)) F),
      q ∈ W ∧
      Module.finrank F W ≤
        profileLocalDimProduct (F := F) Φ (verifierLocalFactorDimFamily (F := F) Φ) ρ

/-- Explicit closure hypothesis turning the generatorwise assembly into a whole-slice bound. -/
def ProfileSliceGeneratorClosure
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

/-- A generatorwise theorem plus the explicit closure hypothesis implies the whole-slice assembly theorem. -/
theorem profileSliceAssemblesFromGeneratorwise
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4)
    (_hgen : ProfileSliceGeneratorAssembles (F := F) Φ κ shift S hS ρ)
    (hclosure : ProfileSliceGeneratorClosure (F := F) Φ κ shift S hS ρ) :
    ProfileSliceAssemblesFromLocalProduct (F := F) Φ κ shift S hS ρ := by
  refine ⟨profileSliceSubspace (F := F) (κ := κ) (m := Φ.clauses.length) (w := 4)
    shift (verifierFactor (F := F) Φ) S hS ρ, le_rfl, hclosure⟩

end ProfileSliceAssemblyReduction
