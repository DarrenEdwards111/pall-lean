import PallLean.IndicatorInsertReduction

/-!
# SupportIndicatorInsertProof

A genuinely proved atomic fact for the remaining ambient insert-step.
-/

namespace SupportIndicatorInsertProof

open SPDP
open MultilinearSPDP
open IndicatorMonomialCalcReduction
open IndicatorInsertReduction

variable {F : Type*} [Field F] [Nontrivial F]

theorem supportIndicatorInsertUpdate
    (n : ℕ) :
    SupportIndicatorInsertUpdate (F := F) n := by
  intro U u hu
  ext i
  by_cases hi : i = u
  · subst hi
    simp [supportIndicator, hu]
  · by_cases hUi : i ∈ U
    · simp [supportIndicator, hi, hUi]
    · simp [supportIndicator, hi, hUi]

end SupportIndicatorInsertProof
