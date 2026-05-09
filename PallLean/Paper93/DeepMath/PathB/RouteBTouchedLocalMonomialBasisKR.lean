import PallLean.Paper93.DeepMath.PathB.RouteBTouchedRowWindowSupportKR
import PallLean.WithinProfileBound

/-!
# Route B touched local monomial basis

The touched part of a product-rule row is genuinely local: after multilinear
projection it is supported on the radius-1 row window, whose size is at most
`3 log n`.  This file turns that locality into the exact finite monomial-basis
span used by the KR/profile argument.

Crucially, this only spans the touched local product.  The untouched background
product is not dropped and is not claimed to be local; it remains the separate
profile/monoid normal-form obligation.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open Step4Compiler
open scoped BigOperators

/-- The multilinear projection of the touched local monomial product lies in
the monomial basis span on the row-local window. -/
theorem mlProj_touchedMonomialLocalPart_mem_rowWindowMonomialSpan
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S T : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (alloc : cookLevinConstraintIdx M n hn2 htb hns →
      List (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hT : T ⊆ S) :
    MultilinearSPDP.mlProj
      (touchedShiftMonomial T *
        touchedAllocatedProductOnly M n hn2 htb hns S.toList alloc) ∈
      Submodule.span ℚ
        (↑(MlProjFar.mlMonomialBasis
          (cookLevinRowLocalWindow M n hn2 htb hns S.toList)) : Set
          (MvPolynomial (Fin (cookLevinTableau M n hn2 htb hns).numVars) ℚ)) := by
  classical
  apply MlProjFar.mlProj_in_span_of_vars_subset
  · intro α hα
    exact WithinProfileBound.isMultilinear_of_mem_mlProj_support
      (touchedShiftMonomial T *
        touchedAllocatedProductOnly M n hn2 htb hns S.toList alloc) α hα
  · intro v hv
    exact touchedMonomialLocalPart_vars_subset_rowLocalWindow
      M n hn2 htb hns S T alloc hT
      (WithinProfileBound.vars_mlProj_subset
        (touchedShiftMonomial T *
          touchedAllocatedProductOnly M n hn2 htb hns S.toList alloc) hv)

/-- The touched local monomial basis has at most `2^(3 log₂ n)` generators. -/
theorem touchedRowWindowMonomialBasis_card_le_two_pow_three_log
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hS : S.card ≤ Nat.log 2 n) :
    (MlProjFar.mlMonomialBasis
      (cookLevinRowLocalWindow M n hn2 htb hns S.toList)).card ≤
        2 ^ (3 * Nat.log 2 n) := by
  classical
  have hbasis := MlProjFar.mlMonomialBasis_card
    (cookLevinRowLocalWindow M n hn2 htb hns S.toList)
  have hwin : (cookLevinRowLocalWindow M n hn2 htb hns S.toList).card ≤
      3 * Nat.log 2 n := by
    have h0 := cookLevinRowLocalWindow_card_le_three_mul M n hn2 htb hns S.toList
    have hto : S.toList.toFinset.card ≤ Nat.log 2 n := by
      simpa using hS
    exact h0.trans (Nat.mul_le_mul_left 3 hto)
  exact hbasis.trans (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hwin)

/-- Same bound written as `8^(log₂ n)`, the local `C₃^κ` accounting form. -/
theorem touchedRowWindowMonomialBasis_card_le_eight_pow_log
    (M : DTM) (n : ℕ) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hS : S.card ≤ Nat.log 2 n) :
    (MlProjFar.mlMonomialBasis
      (cookLevinRowLocalWindow M n hn2 htb hns S.toList)).card ≤
        8 ^ Nat.log 2 n := by
  have h := touchedRowWindowMonomialBasis_card_le_two_pow_three_log
    M n hn2 htb hns S hS
  simpa [show (8 : ℕ) = 2 ^ 3 by norm_num, pow_mul] using h

/-- The touched local basis fits under the same `n^200` polynomial envelope at
paper scale. -/
theorem touchedRowWindowMonomialBasis_card_le_n_pow_200
    (M : DTM) (n : ℕ) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S : Finset (Fin (cookLevinTableau M n hn2 htb hns).numVars))
    (hS : S.card ≤ Nat.log 2 n) :
    (MlProjFar.mlMonomialBasis
      (cookLevinRowLocalWindow M n hn2 htb hns S.toList)).card ≤ n ^ 200 := by
  have h8 := touchedRowWindowMonomialBasis_card_le_eight_pow_log
    M n hn2 htb hns S hS
  have hC : Nat.log 2 8 + 1 ≤ 200 := by norm_num
  exact h8.trans (touchedKR_constant_card_le_n_pow_200 8 n hn hC)

/-! ## Axiom audit anchors -/

#print axioms mlProj_touchedMonomialLocalPart_mem_rowWindowMonomialSpan
#print axioms touchedRowWindowMonomialBasis_card_le_two_pow_three_log
#print axioms touchedRowWindowMonomialBasis_card_le_eight_pow_log
#print axioms touchedRowWindowMonomialBasis_card_le_n_pow_200

end PallLean.Paper93.DeepMath.PathB
