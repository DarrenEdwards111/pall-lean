import PallLean.BoundedProfileLift
import PallLean.TseitinProfileReduction

/-!
# VerifierProfileSlices

Concrete width-4 profile slices for the Tseitin verifier product.

This file packages the work already done into a single concrete slice family for
`tseitinPoly`, and proves the coverage reduction from genuine multilinear blocked-SPDP
generators to those profile slices.

It does not yet prove the polynomial per-profile dimension bound; that remains the
next substantive mathematical step.
-/

namespace VerifierProfileSlices

open SPDP
open MultilinearSPDP
open Tseitin
open ProductTransport
open ProductProfileSlices
open BoundedProfileLift
open TseitinProfileReduction
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Concrete width-4 verifier profile slices for a fixed derivative list and shift. -/
noncomputable def verifierProfileSliceFamily
    (Φ : TseitinFormula)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ))) (hS : S.length = κ) :
    ProfileSliceFamily (tseitinNumVars Φ) Φ.clauses.length 4 F :=
  profileSliceFamily (F := F) (κ := κ) (m := Φ.clauses.length) (w := 4)
    shift (verifierFactor (F := F) Φ) S hS

/-- The shifted allocation span of the verifier is covered by the width-4 profile slices. -/
theorem verifierAllocSpan_covered_by_profileSlices
    (Φ : TseitinFormula)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ))) (hS : S.length = κ)
    (hS_nodup : S.Nodup) :
    verifierAllocSpan (F := F) (κ := κ) Φ shift S hS ≤
      ⨆ ρ : ProfileIndex Φ.clauses.length 4,
        verifierProfileSliceFamily (F := F) (κ := κ) Φ shift S hS ρ := by
  simpa [verifierProfileSliceFamily] using
    verifierAllocSpan_le_profileSlices (F := F) (κ := κ) Φ shift S hS hS_nodup

/-- A single genuine multilinear blocked-SPDP verifier generator is covered by the width-4 slices. -/
theorem mlGenerator_coupledVerifier_mem_profileSlices
    (Φ : TseitinFormula)
    (S : List (Fin (tseitinNumVars Φ)))
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (hS : S.length = κ)
    (hdeg : shift.totalDegree ≤ ℓ)
    (hvars : shift.vars ⊆ S.toFinset)
    (hadm : isBlockAdmissible (tseitinPartition Φ.graph.numVertices) S) :
    mlProj (shift * iterDerivList S (coupledVerifier F Φ)) ∈
      ⨆ ρ : ProfileIndex Φ.clauses.length 4,
        verifierProfileSliceFamily (F := F) (κ := κ) Φ shift S hS ρ := by
  have htransport := mlBlockedSpdp_generator_coupledVerifier_mem_allocSpan
    (F := F) (κ := κ) Φ S shift hS hdeg hvars hadm
  have hcover := verifierAllocSpan_covered_by_profileSlices
    (F := F) (κ := κ) Φ shift S hS hadm.1
  exact hcover htransport

/--
Concrete coverage statement parameterized by genuine multilinear blocked-SPDP generators.

This is the verifier-side coverage ingredient needed by the profile-compression route.
-/
def ConcreteVerifierCoverage
    (Φ : TseitinFormula) (κ ℓ : ℕ) : Prop :=
  ∀ (S : List (Fin (tseitinNumVars Φ)))
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F),
    S.length = κ →
    shift.totalDegree ≤ ℓ →
    shift.vars ⊆ S.toFinset →
    isBlockAdmissible (tseitinPartition Φ.graph.numVertices) S →
    mlProj (shift * iterDerivList S (coupledVerifier F Φ)) ∈
      ⨆ ρ : ProfileIndex Φ.clauses.length 4,
        verifierProfileSliceFamily (F := F) (κ := κ) Φ shift S (by assumption) ρ

/-- The concrete coverage statement holds for the verifier product. -/
theorem concreteVerifierCoverage
    (Φ : TseitinFormula) (κ ℓ : ℕ) :
    ConcreteVerifierCoverage (F := F) Φ κ ℓ := by
  intro S shift hS hdeg hvars hadm
  simpa [ConcreteVerifierCoverage, verifierProfileSliceFamily] using
    mlGenerator_coupledVerifier_mem_profileSlices
      (F := F) (κ := κ) (ℓ := ℓ) Φ S shift hS hdeg hvars hadm

end VerifierProfileSlices
