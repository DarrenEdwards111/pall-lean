import PallLean.ProfileAllocationCountReduction

/-!
# ProfileMultinomialReduction

Final profile-side reduction.

The remaining counting target is purely combinatorial: bound the number of derivative allocations
realizing a fixed bounded profile. This is a multinomial-count problem. This file isolates that
statement as the exact remaining target.
-/

namespace ProfileMultinomialReduction

open SPDP
open MultilinearSPDP
open Tseitin
open LocalFactorReduction
open LocalClauseFactorSpace
open ProfileAllocationCountReduction
open ProductProfileSlices
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Pure combinatorial multinomial-style bound for allocations with a fixed profile. -/
def FixedProfileAllocationCountBound
    (Φ : TseitinFormula)
    (κ : ℕ)
    (ρ : ProfileIndex Φ.clauses.length 4) : Prop :=
  (allocationsWithProfile (F := F) Φ κ ρ).card + 1
    ≤ profileLocalDimProduct (F := F) Φ (verifierLocalFactorDimFamily (F := F) Φ) ρ

/-- The explicit multinomial-style count bound is exactly the remaining profile counting target. -/
theorem allocationsWithProfileCardBound_is_fixedProfileCount
    (Φ : TseitinFormula)
    (κ : ℕ)
    (ρ : ProfileIndex Φ.clauses.length 4)
    (hcount : FixedProfileAllocationCountBound (F := F) Φ κ ρ) :
    AllocationsWithProfileCardBound (F := F) Φ κ ρ :=
  hcount

/-- Therefore the fixed-profile counting theorem implies the profile-family cardinality bound. -/
theorem profileAllocationFamilyCardBound_of_fixedProfileCount
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4)
    (hcount : FixedProfileAllocationCountBound (F := F) Φ κ ρ) :
    ProfileAllocationFamilyCardBound (F := F) Φ κ shift S hS ρ := by
  exact profileAllocationFamilyCardBound_of_allocationCount
    (F := F) Φ κ shift S hS ρ hcount

end ProfileMultinomialReduction
