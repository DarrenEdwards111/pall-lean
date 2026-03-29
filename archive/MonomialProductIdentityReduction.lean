import PallLean.MonomialSupportIdentityReduction
import PallLean.ExponentIndicatorProof

/-!
# MonomialProductIdentityReduction

Further reduction of the remaining ambient-side frontier.

After proving that a multilinear exponent vector is the indicator of its support, the
only remaining content is the pure algebraic calculation that the corresponding monomial
is the scalar multiple of the product of variables over that support.
-/

namespace MonomialProductIdentityReduction

open SPDP
open MultilinearSPDP
open SupportAmbientBasisReduction
open MonomialSupportIdentityReduction
open ExponentIndicatorReduction
open ExponentIndicatorProof
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Pure algebraic calculation for support-indicator exponent vectors. -/
def SupportIndicatorMonomialEqProduct {n : ℕ} : Prop :=
  ∀ (α : Fin n →₀ ℕ) (a : F),
    (∀ i : Fin n, α i = if i ∈ α.support then 1 else 0) →
    MvPolynomial.monomial α a = a • squarefreeMonomial (F := F) α.support

/-- The pure product calculation implies the remaining ambient monomial theorem. -/
theorem monomialOfSupportIndicatorEqSquarefree_of_productCalc
    {n : ℕ}
    (hprod : SupportIndicatorMonomialEqProduct (F := F) (n := n)) :
    MonomialOfSupportIndicatorEqSquarefree (F := F) (n := n) := by
  intro α a hind
  exact hprod α a hind

/-- Combined ambient-side package: one proved atomic fact plus one remaining pure calculation. -/
theorem multilinearMonomialEqSquarefree_of_productCalc
    {n : ℕ}
    (hprod : SupportIndicatorMonomialEqProduct (F := F) (n := n)) :
    MultilinearMonomialEqSquarefree (F := F) (n := n) := by
  apply multilinearMonomialEqSquarefree_of_atomicFacts
  · exact multilinearExponentIsSupportIndicator_of_supportValue (n := n) supportMemberHasValueOne
  · exact monomialOfSupportIndicatorEqSquarefree_of_productCalc (F := F) hprod

end MonomialProductIdentityReduction
