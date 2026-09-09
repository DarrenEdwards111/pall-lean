import GodMoveFaithfulHandshake

/-!
# Unsatisfiable signed CNFs have zero Boolean characteristic target

This file concerns the genuine signed `CookLevinReduction.Formula` semantics
and the canonical interpolation target in `GodMoveFaithfulHandshake`.
Every unsatisfiable formula has identically zero characteristic polynomial,
and therefore zero strict and inclusive SPDP rank at every parameter choice.
With faithful machine correctness, the corresponding pinned-query source is
also zero.

The distinction between candidate families matters: an unsatisfiable Tseitin
contradiction cannot have a positive minor in THIS characteristic target.
This statement does not apply indiscriminately to satisfiable families or to
raw gadget products that have not been identified with this polynomial.
It also says nothing against the intended use of a conditional contradiction
under a hypothetical polynomial-time SAT decider in a different construction.
-/

namespace GodMoveCharacteristicUnsat

open GodMoveBooleanInterpolation GodMovePinnedSATQueries GodMoveFaithfulHandshake
open MultilinearSPDP SPDP
open PallLean.Paper93.DeepMath.PathB
open CookLevinReduction ComposableMachine SeparationTarget

/-- Unsatisfiability excludes every finite assignment's default-false extension.
No bound on the variables occurring in the formula is needed in this direction. -/
theorem evalFormula_extendAssignment_eq_false_of_unsatisfiable
    {n : ℕ} (φ : Formula) (hunsat : ¬ Satisfiable φ) (a : Assignment n) :
    evalFormula (extendAssignment a) φ = false := by
  cases heval : evalFormula (extendAssignment a) φ with
  | false => rfl
  | true => exact False.elim (hunsat ⟨extendAssignment a, heval⟩)

/-- The exact canonical characteristic polynomial of an unsatisfiable formula
is zero, not merely a polynomial that vanishes at Boolean points. -/
theorem verifierCharacteristic_eq_zero_of_unsatisfiable
    (n : ℕ) (φ : Formula) (hunsat : ¬ Satisfiable φ) :
    verifierCharacteristic n φ = 0 := by
  calc
    verifierCharacteristic n φ = interpolate (fun _ : Assignment n => false) :=
      interpolate_congr (evalFormula_extendAssignment_eq_false_of_unsatisfiable φ hunsat)
    _ = 0 := by
      rw [interpolate_eq_weighted_sum]
      simp

/-- Faithful operational correctness transfers the exact zero target to the
source made from all concretely encoded assignment-pinned queries. -/
theorem machineQueryPolynomial_eq_zero_of_unsatisfiable
    {n : ℕ} (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (hvars : VariablesBelow n φ) (hunsat : ¬ Satisfiable φ) :
    machineQueryPolynomial (n := n) M T φ = 0 := by
  rw [machineQueryPolynomial_eq_verifierCharacteristic M T hD φ hvars]
  exact verifierCharacteristic_eq_zero_of_unsatisfiable n φ hunsat

theorem verifierCharacteristic_strict_rank_eq_zero_of_unsatisfiable
    {n : ℕ} (φ : Formula) (hunsat : ¬ Satisfiable φ)
    (B : BlockPartition n) (kappa ell : ℕ) :
    mlBlockedSpdpRank B kappa ell (verifierCharacteristic n φ) = 0 := by
  rw [verifierCharacteristic_eq_zero_of_unsatisfiable n φ hunsat,
    mlBlockedSpdpRank_zero]

theorem verifierCharacteristic_inclusive_rank_eq_zero_of_unsatisfiable
    {n : ℕ} (φ : Formula) (hunsat : ¬ Satisfiable φ)
    (B : BlockPartition n) (kappa ell : ℕ) :
    mlBlockedSpdpRankInc B kappa ell (verifierCharacteristic n φ) = 0 := by
  rw [verifierCharacteristic_eq_zero_of_unsatisfiable n φ hunsat]
  simp [mlBlockedSpdpRankInc, mlBlockedSpdpSubspaceInc_zero]

theorem machineQueryPolynomial_strict_rank_eq_zero_of_unsatisfiable
    {n : ℕ} (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (hvars : VariablesBelow n φ) (hunsat : ¬ Satisfiable φ)
    (B : BlockPartition n) (kappa ell : ℕ) :
    mlBlockedSpdpRank B kappa ell (machineQueryPolynomial (n := n) M T φ) = 0 := by
  rw [machineQueryPolynomial_eq_zero_of_unsatisfiable M T hD φ hvars hunsat,
    mlBlockedSpdpRank_zero]

theorem machineQueryPolynomial_inclusive_rank_eq_zero_of_unsatisfiable
    {n : ℕ} (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    (φ : Formula) (hvars : VariablesBelow n φ) (hunsat : ¬ Satisfiable φ)
    (B : BlockPartition n) (kappa ell : ℕ) :
    mlBlockedSpdpRankInc B kappa ell (machineQueryPolynomial (n := n) M T φ) = 0 := by
  rw [machineQueryPolynomial_eq_zero_of_unsatisfiable M T hD φ hvars hunsat]
  simp [mlBlockedSpdpRankInc, mlBlockedSpdpSubspaceInc_zero]

end GodMoveCharacteristicUnsat

#print axioms GodMoveCharacteristicUnsat.evalFormula_extendAssignment_eq_false_of_unsatisfiable
#print axioms GodMoveCharacteristicUnsat.verifierCharacteristic_eq_zero_of_unsatisfiable
#print axioms GodMoveCharacteristicUnsat.machineQueryPolynomial_eq_zero_of_unsatisfiable
#print axioms GodMoveCharacteristicUnsat.verifierCharacteristic_strict_rank_eq_zero_of_unsatisfiable
#print axioms GodMoveCharacteristicUnsat.verifierCharacteristic_inclusive_rank_eq_zero_of_unsatisfiable
#print axioms GodMoveCharacteristicUnsat.machineQueryPolynomial_strict_rank_eq_zero_of_unsatisfiable
#print axioms GodMoveCharacteristicUnsat.machineQueryPolynomial_inclusive_rank_eq_zero_of_unsatisfiable
