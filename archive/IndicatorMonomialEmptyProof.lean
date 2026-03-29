import PallLean.IndicatorMonomialInductionReduction

/-!
# IndicatorMonomialEmptyProof

A genuinely proved base case for the remaining ambient-side induction theorem.
-/

namespace IndicatorMonomialEmptyProof

open SPDP
open MultilinearSPDP
open SupportAmbientBasisReduction
open IndicatorMonomialCalcReduction
open IndicatorMonomialInductionReduction
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

theorem indicatorMonomialEmpty
    (n : ℕ) :
    IndicatorMonomialEmpty (F := F) n := by
  intro a
  unfold supportIndicator squarefreeMonomial
  simp

end IndicatorMonomialEmptyProof
