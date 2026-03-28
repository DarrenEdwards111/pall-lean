import PallLean.IndicatorInsertReduction

/-!
# MonomialMulXReduction

Final reduction of the remaining ambient insert-step algebra.

The statement

  X u * monomial α a = monomial (single u 1 + α) a

is just the standard monomial multiplication identity specialized to `X u = monomial (single u 1) 1`.
This file packages that reduction explicitly.
-/

namespace MonomialMulXReduction

open SPDP
open MultilinearSPDP
open IndicatorInsertReduction
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Standard monomial multiplication formula. -/
def MonomialMulFormula (n : ℕ) : Prop :=
  ∀ (α β : Fin n →₀ ℕ) (a b : F),
    MvPolynomial.monomial α a * MvPolynomial.monomial β b =
      MvPolynomial.monomial (α + β) (a * b)

/-- The standard monomial multiplication formula implies `MonomialMulXSingle`. -/
theorem monomialMulXSingle_of_formula
    (n : ℕ)
    (hmono : MonomialMulFormula (F := F) n) :
    MonomialMulXSingle (F := F) n := by
  intro α u a
  change MvPolynomial.monomial (Finsupp.single u 1) (1 : F) * MvPolynomial.monomial α a = _
  simpa using hmono (Finsupp.single u 1) α (1 : F) a

end MonomialMulXReduction
