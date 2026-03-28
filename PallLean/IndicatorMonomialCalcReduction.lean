import PallLean.MonomialProductIdentityReduction

/-!
# IndicatorMonomialCalcReduction

Final ambient-side reduction.

The remaining ambient theorem is now reduced to the explicit calculation that the monomial
with indicator exponents for a finite support set `U` equals the product of the corresponding
variables. This is the pure algebraic endpoint of the squarefree side.
-/

namespace IndicatorMonomialCalcReduction

open SPDP
open MultilinearSPDP
open SupportAmbientBasisReduction
open MonomialProductIdentityReduction
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Indicator exponent vector of a finite support set. -/
noncomputable def supportIndicator {n : ℕ} (U : Finset (Fin n)) : Fin n →₀ ℕ :=
  Finsupp.onFinset U (fun _ => 1) (by intro _ _; rfl)

/-- Pure indicator-monomial calculation. -/
def IndicatorMonomialEqSquarefreeProduct {n : ℕ} : Prop :=
  ∀ (U : Finset (Fin n)) (a : F),
    MvPolynomial.monomial (supportIndicator U) a = a • squarefreeMonomial (F := F) U

/-- The pure indicator calculation implies the remaining support-indicator product theorem. -/
theorem supportIndicatorMonomialEqProduct_of_indicatorCalc
    {n : ℕ}
    (hcalc : IndicatorMonomialEqSquarefreeProduct (F := F) (n := n)) :
    SupportIndicatorMonomialEqProduct (F := F) (n := n) := by
  intro α a hind
  -- α is determined pointwise by its support indicator, so reduce to the explicit indicator calculation.
  have hα : α = supportIndicator α.support := by
    ext i
    simp [supportIndicator, hind i]
  rw [hα]
  exact hcalc α.support a

end IndicatorMonomialCalcReduction
