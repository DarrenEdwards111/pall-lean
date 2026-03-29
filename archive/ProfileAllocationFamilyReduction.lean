import PallLean.ProfileSpanClosureReduction

/-!
# ProfileAllocationFamilyReduction

This file makes the profile-side closure theorem concrete.

A profile slice is by definition spanned by allocation-generated polynomials with a fixed
profile. Because derivative allocations form a finite type, the slice is automatically spanned
by an explicit finite family obtained from `Finset.univ.image`.  The only remaining content is
therefore the cardinality bound for that family.
-/

namespace ProfileAllocationFamilyReduction

open SPDP
open MultilinearSPDP
open Tseitin
open LocalFactorReduction
open LocalClauseFactorSpace
open ProfileSpanClosureReduction
open ProductProfileSlices
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- The explicit finite family of allocation-generated polynomials for a fixed profile. -/
noncomputable def profileAllocationFamily
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4) :
    Finset (MvPolynomial (Fin (tseitinNumVars Φ)) F) :=
  (Finset.univ : Finset (DerivAlloc κ Φ.clauses.length)).image (fun α =>
    if hbounded : ∀ i, allocProfile α i ≤ 4 then
      if allocProfileIndex α hbounded = ρ then
        shiftedAllocGenerator shift (verifierFactor (F := F) Φ) S hS α
      else 0
    else 0)

/-- The concrete profile slice is spanned by the explicit finite allocation family. -/
theorem profileSlice_le_span_profileAllocationFamily
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4) :
    profileSliceSubspace (F := F) (κ := κ) (m := Φ.clauses.length) (w := 4)
      shift (verifierFactor (F := F) Φ) S hS ρ
      ≤ Submodule.span F (↑(profileAllocationFamily (F := F) Φ κ shift S hS ρ) :
        Set (MvPolynomial (Fin (tseitinNumVars Φ)) F)) := by
  unfold profileSliceSubspace
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨α, hbounded, hρ, rfl⟩
  apply Submodule.subset_span
  change shiftedAllocGenerator shift (verifierFactor (F := F) Φ) S hS α ∈
    ↑(profileAllocationFamily (F := F) Φ κ shift S hS ρ)
  unfold profileAllocationFamily
  apply Finset.mem_image.mpr
  refine ⟨α, Finset.mem_univ _, ?_⟩
  simp [hbounded, hρ]

/-- Remaining concrete counting theorem for the explicit allocation family. -/
def ProfileAllocationFamilyCardBound
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4) : Prop :=
  (profileAllocationFamily (F := F) Φ κ shift S hS ρ).card
    ≤ profileLocalDimProduct (F := F) Φ (verifierLocalFactorDimFamily (F := F) Φ) ρ

/-- The explicit allocation-family cardinality bound implies the profile slice finite spanning theorem. -/
theorem profileSliceHasFiniteSpanningFamily_of_allocationFamilyCardBound
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4)
    (hcard : ProfileAllocationFamilyCardBound (F := F) Φ κ shift S hS ρ) :
    ProfileSliceHasFiniteSpanningFamily (F := F) Φ κ shift S hS ρ := by
  refine ⟨profileAllocationFamily (F := F) Φ κ shift S hS ρ, ?_, hcard⟩
  exact profileSlice_le_span_profileAllocationFamily (F := F) Φ κ shift S hS ρ

end ProfileAllocationFamilyReduction
