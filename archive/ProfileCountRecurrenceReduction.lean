import PallLean.ProfileMultinomialReduction

/-!
# ProfileCountRecurrenceReduction

Final recurrence-shaped reduction for the remaining profile-side counting theorem.

The counting problem is now purely combinatorial: count derivative allocations realizing a
fixed bounded profile. This file packages the exact recurrence-shaped target needed to close it.
-/

namespace ProfileCountRecurrenceReduction

open SPDP
open MultilinearSPDP
open Tseitin
open LocalFactorReduction
open LocalClauseFactorSpace
open ProfileMultinomialReduction
open ProductProfileSlices
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Pure recurrence/closed-form counting target for allocations with a fixed profile. -/
def FixedProfileAllocationCountRecurrence
    (Φ : TseitinFormula)
    (κ : ℕ)
    (ρ : ProfileIndex Φ.clauses.length 4) : Prop :=
  (allocationsWithProfile (F := F) Φ κ ρ).card + 1
    ≤ ∏ i : Fin Φ.clauses.length, (ρ i).val + 1

/-- The recurrence-shaped count target implies the remaining profile local-dimension bound,
since the local dimension family is constantly `16` and hence dominates `(ρ i).val + 1 ≤ 5`. -/
theorem fixedProfileAllocationCountBound_of_recurrence
    (Φ : TseitinFormula)
    (κ : ℕ)
    (ρ : ProfileIndex Φ.clauses.length 4)
    (hrec : FixedProfileAllocationCountRecurrence (F := F) Φ κ ρ) :
    FixedProfileAllocationCountBound (F := F) Φ κ ρ := by
  have hdom : (∏ i : Fin Φ.clauses.length, (ρ i).val + 1)
      ≤ profileLocalDimProduct (F := F) Φ (verifierLocalFactorDimFamily (F := F) Φ) ρ := by
    unfold profileLocalDimProduct verifierLocalFactorDimFamily
    apply Finset.prod_le_prod
    · intro i _
      have : (ρ i).val + 1 ≤ 5 := by
        exact Nat.succ_le_of_lt (ρ i).isLt
      omega
    · intro i _
      omega
  exact le_trans hrec hdom

end ProfileCountRecurrenceReduction
