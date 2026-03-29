import PallLean.SquarefreeMonomialIdentityReduction

/-!
# MonomialSupportIdentityReduction

Final atomic reduction on the ambient side, one step lower.

For a multilinear exponent vector `α`, the statement

  monomial α a = a • squarefreeMonomial α.support

reduces to the support/exponent fact that `α` is exactly the indicator of its support,
together with the explicit monomial/product identity calculation.
-/

namespace MonomialSupportIdentityReduction

open SPDP
open MultilinearSPDP
open SupportAmbientBasisReduction
open SquarefreeMonomialIdentityReduction
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Atomic support/exponent identity for multilinear exponent vectors. -/
def MultilinearExponentIsSupportIndicator {n : ℕ} : Prop :=
  ∀ (α : Fin n →₀ ℕ),
    Finsupp.IsMultilinear α →
    ∀ i : Fin n, α i = if i ∈ α.support then 1 else 0

/-- Explicit monomial/product identity once the exponent vector is known to be the support indicator. -/
def MonomialOfSupportIndicatorEqSquarefree {n : ℕ} : Prop :=
  ∀ (α : Fin n →₀ ℕ) (a : F),
    (∀ i : Fin n, α i = if i ∈ α.support then 1 else 0) →
    MvPolynomial.monomial α a = a • squarefreeMonomial (F := F) α.support

/-- The two atomic support-side facts imply the squarefree monomial identity. -/
theorem multilinearMonomialEqSquarefree_of_atomicFacts
    {n : ℕ}
    (hind : MultilinearExponentIsSupportIndicator (n := n))
    (hmono : MonomialOfSupportIndicatorEqSquarefree (F := F) (n := n)) :
    MultilinearMonomialEqSquarefree (F := F) (n := n) := by
  intro α a hml
  exact hmono α a (hind α hml)

end MonomialSupportIdentityReduction
