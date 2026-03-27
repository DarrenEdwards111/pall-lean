import PallLean.SupportAmbientBasisReduction
import PallLean.AssemblyMapReduction

/-!
# TseitinSpdpReplacementRoute

Single integration point for replacing the frontier axiom
`MultilinearSPDP.tseitin_spdp_rank_bound` with the profile-compression route
formalized on `godmove-paper-faithful`.

This file does not prove the final theorem by itself. It packages the exact local
hypotheses now remaining on the branch and derives the polynomial verifier-side
shape from them.
-/

namespace TseitinSpdpReplacementRoute

open SPDP
open MultilinearSPDP
open Tseitin
open LocalAmbientReduction
open SupportAmbientBasisReduction
open ProfileAssemblyReduction
open AssemblyMapReduction
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- The two remaining concrete local theorems needed to replace the verifier-side axiom. -/
structure TseitinProfileCompressionPackage (Φ : TseitinFormula) (κ : ℕ) where
  squarefree_span : ∀ T : Finset (Fin (tseitinNumVars Φ)),
    SupportAmbientSpannedBySquarefree (F := F) T
  assembly : VerifierProfileAssemblyTheorem (F := F) Φ κ

/--
From the local package, derive the polynomial per-profile slice bound in the current
paper-faithful reduction pipeline.
-/
theorem verifier_profile_slices_poly_of_package
    (Φ : TseitinFormula)
    (κ : ℕ)
    (pkg : TseitinProfileCompressionPackage (F := F) Φ κ) :
    ∀ (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
      (S : List (Fin (tseitinNumVars Φ)))
      (hS : S.length = κ)
      (ρ : ProfileIndex Φ.clauses.length 4),
      Module.finrank F
        (profileSliceSubspace (F := F) (κ := κ) (m := Φ.clauses.length) (w := 4)
          shift (verifierFactor (F := F) Φ) S hS ρ)
      ≤ Φ.graph.numVertices ^ (16 * 10) := by
  have hambient : SupportAmbientFinrankBound (F := F) (n := tseitinNumVars Φ) :=
    supportAmbient_finrankBound_of_squarefree (F := F) pkg.squarefree_span
  have hlocalEmbed : LocalClauseFactorEmbedsInAmbient (F := F) Φ :=
    LocalClauseFactorEmbedsInAmbient_proved (F := F) Φ
  exact verifierProfileSlices_poly_of_local_and_assembly
    (F := F) Φ κ hlocalEmbed hambient pkg.assembly

end TseitinSpdpReplacementRoute
