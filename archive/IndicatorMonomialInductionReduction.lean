import PallLean.IndicatorMonomialCalcReduction

/-!
# IndicatorMonomialInductionReduction

Final induction-shaped reduction for the ambient-side algebra theorem.

To prove that the indicator monomial equals the squarefree product for any finite support set,
it is enough to prove:

* the empty-set base case;
* the insert-step recursion for `supportIndicator` and `squarefreeMonomial`.
-/

namespace IndicatorMonomialInductionReduction

open SPDP
open MultilinearSPDP
open SupportAmbientBasisReduction
open IndicatorMonomialCalcReduction
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Empty-set base case for the indicator monomial calculation. -/
def IndicatorMonomialEmpty (n : ℕ) : Prop :=
  ∀ a : F,
    MvPolynomial.monomial (supportIndicator (F := F) (n := n) (∅ : Finset (Fin n))) a =
      a • squarefreeMonomial (F := F) (∅ : Finset (Fin n))

/-- Insert-step recursion for the indicator monomial calculation. -/
def IndicatorMonomialInsertStep (n : ℕ) : Prop :=
  ∀ (U : Finset (Fin n)) (u : Fin n) (hu : u ∉ U) (a : F),
    MvPolynomial.monomial (supportIndicator (F := F) (insert u U)) a =
      (X u : MvPolynomial (Fin n) F) * MvPolynomial.monomial (supportIndicator (F := F) U) a

/-- Empty case plus insert step imply the full indicator-monomial product theorem. -/
theorem indicatorMonomialEqSquarefreeProduct_of_induction
    {n : ℕ}
    (hempty : IndicatorMonomialEmpty (F := F) n)
    (hstep : IndicatorMonomialInsertStep (F := F) n) :
    IndicatorMonomialEqSquarefreeProduct (F := F) (n := n) := by
  intro U a
  induction U using Finset.induction_on with
  | empty =>
      simpa using hempty a
  | @insert u U hu ih =>
      rw [hstep U u hu a, ih]
      unfold squarefreeMonomial
      rw [Finset.prod_insert hu]
      simp [smul_eq_mul, mul_assoc]

end IndicatorMonomialInductionReduction
