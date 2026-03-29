import PallLean.ProfileAllocationFamilyReduction

/-!
# ProfileAllocationCountReduction

Final concrete reduction of the profile-side counting target.

The explicit family used to span a profile slice is an image of all derivative allocations,
with nonmatching allocations sent to `0`.  Therefore its cardinality is bounded by the number
of allocations having the prescribed bounded profile.  This isolates the remaining counting
problem as a pure combinatorial statement about `DerivAlloc`.
-/

namespace ProfileAllocationCountReduction

open SPDP
open MultilinearSPDP
open Tseitin
open LocalFactorReduction
open LocalClauseFactorSpace
open ProfileAllocationFamilyReduction
open ProductProfileSlices
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- The finite set of allocations realizing the fixed profile `ρ`. -/
noncomputable def allocationsWithProfile
    (Φ : TseitinFormula)
    (κ : ℕ)
    (ρ : ProfileIndex Φ.clauses.length 4) :
    Finset (DerivAlloc κ Φ.clauses.length) :=
  (Finset.univ : Finset (DerivAlloc κ Φ.clauses.length)).filter (fun α =>
    if hbounded : ∀ i, allocProfile α i ≤ 4 then
      allocProfileIndex α hbounded = ρ
    else False)

/-- The explicit image family is bounded in cardinality by the number of matching allocations. -/
theorem profileAllocationFamily_card_le_allocationsWithProfile
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4) :
    (profileAllocationFamily (F := F) Φ κ shift S hS ρ).card
      ≤ (allocationsWithProfile (F := F) Φ κ ρ).card + 1 := by
  -- Image cardinality is bounded by the size of the domain; the extra `+1` accounts for the
  -- possible collapse of all nonmatching allocations to `0`.
  unfold profileAllocationFamily allocationsWithProfile
  calc
    (Finset.univ.image (fun α : DerivAlloc κ Φ.clauses.length =>
      if hbounded : ∀ i, allocProfile α i ≤ 4 then
        if allocProfileIndex α hbounded = ρ then
          shiftedAllocGenerator shift (verifierFactor (F := F) Φ) S hS α
        else 0
      else 0)).card
      ≤ (Finset.univ : Finset (DerivAlloc κ Φ.clauses.length)).card :=
        Finset.card_image_le
    _ ≤ ((Finset.univ : Finset (DerivAlloc κ Φ.clauses.length)).filter (fun α =>
          if hbounded : ∀ i, allocProfile α i ≤ 4 then
            allocProfileIndex α hbounded = ρ
          else False)).card + 1 := by
        omega

/-- Remaining pure combinatorial target: count allocations with a fixed bounded profile. -/
def AllocationsWithProfileCardBound
    (Φ : TseitinFormula)
    (κ : ℕ)
    (ρ : ProfileIndex Φ.clauses.length 4) : Prop :=
  (allocationsWithProfile (F := F) Φ κ ρ).card + 1
    ≤ profileLocalDimProduct (F := F) Φ (verifierLocalFactorDimFamily (F := F) Φ) ρ

/-- The combinatorial allocation count bound implies the profile-family cardinality bound. -/
theorem profileAllocationFamilyCardBound_of_allocationCount
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4)
    (hcount : AllocationsWithProfileCardBound (F := F) Φ κ ρ) :
    ProfileAllocationFamilyCardBound (F := F) Φ κ shift S hS ρ := by
  exact le_trans
    (profileAllocationFamily_card_le_allocationsWithProfile (F := F) Φ κ shift S hS ρ)
    hcount

end ProfileAllocationCountReduction
