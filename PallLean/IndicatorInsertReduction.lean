import PallLean.IndicatorMonomialInductionReduction

/-!
# IndicatorInsertReduction

Further reduction of the remaining ambient-side induction step.

The insert-step identity for indicator monomials splits into two atomic algebraic facts:

1. updating the support-indicator under `insert`;
2. multiplying a monomial by `X u` updates the exponent at `u` from `0` to `1`.
-/

namespace IndicatorInsertReduction

open SPDP
open MultilinearSPDP
open IndicatorMonomialCalcReduction
open IndicatorMonomialInductionReduction
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Support-indicator update under insertion of a fresh element. -/
def SupportIndicatorInsertUpdate (n : ℕ) : Prop :=
  ∀ (U : Finset (Fin n)) (u : Fin n) (hu : u ∉ U),
    supportIndicator (F := F) (n := n) (insert u U) =
      Finsupp.single u 1 + supportIndicator (F := F) (n := n) U

/-- Monomial multiplication by `X u` updates exponents by adding `single u 1`. -/
def MonomialMulXSingle (n : ℕ) : Prop :=
  ∀ (α : Fin n →₀ ℕ) (u : Fin n) (a : F),
    (X u : MvPolynomial (Fin n) F) * MvPolynomial.monomial α a =
      MvPolynomial.monomial (Finsupp.single u 1 + α) a

/-- These two atomic facts imply the remaining insert-step identity. -/
theorem indicatorMonomialInsertStep_of_atomicFacts
    {n : ℕ}
    (hupd : SupportIndicatorInsertUpdate (F := F) n)
    (hmul : MonomialMulXSingle (F := F) n) :
    IndicatorMonomialInsertStep (F := F) n := by
  intro U u hu a
  rw [hupd U u hu, hmul]

end IndicatorInsertReduction
