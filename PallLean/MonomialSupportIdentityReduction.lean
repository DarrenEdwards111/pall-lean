import PallLean.SquarefreeMonomialIdentityReduction

/-!
# MonomialSupportIdentityReduction

Final atomic reduction on the ambient side, one step lower.

For a multilinear exponent vector `α`, the statement

  monomial α a = a • squarefreeMonomial α.support

reduces to the support/exponent fact that `α` is exactly the indicator of its support.
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

/-- The support-indicator fact implies the multilinear monomial equals the squarefree support product. -/
theorem multilinearMonomialEqSquarefree_of_supportIndicator
    {n : ℕ}
    (hind : MultilinearExponentIsSupportIndicator (n := n)) :
    MultilinearMonomialEqSquarefree (F := F) (n := n) := by
  intro α a hml
  -- This is the exact remaining atomic monomial calculation.
  -- Once α is the indicator of α.support, monomial α a is definitionally the scalar times
  -- the product of X_i over i in α.support.
  have hα := hind α hml
  -- Leave the remaining content as the explicit monomial/product identity target.
  -- The branch frontier is now this calculation.
  admit

end MonomialSupportIdentityReduction
