import GodMoveFaithfulHandshake
import GodMoveMonomialMinor

/-!
# A matched calibration for the new characteristic target

The CNF consisting of all positive unit clauses has exactly one satisfying
assignment on its variables. Its canonical characteristic polynomial is
`prod_i X_i`. We construct a product program using exactly `n` variable
references and `n` multiplications (starting at `1`) and prove it evaluates
to this characteristic polynomial. Nevertheless its actual strict and
inclusive SPDP ranks are at least `choose n k`, with an explicit identity
coefficient minor.

This is an easy unit-CNF family, not the required NP-hard instance family.
It supplies neither an efficient extraction for arbitrary SAT nor a
polynomial common-span theorem for hypothetical polynomial-time SAT deciders.
It tests the invalid inference from a short product program to small SPDP rank.
-/

namespace GodMoveUnitCharacteristic

open MvPolynomial SPDP MultilinearSPDP
open GodMoveBooleanInterpolation GodMovePinnedSATQueries GodMoveFaithfulHandshake
open GodMoveMonomialMinor (fullMonomial discreteBlocks KSubset complementaryColumn)
open PallLean.Paper93.DeepMath.PathB
open ComposableMachine CookLevinReduction SeparationTarget
open scoped BigOperators

def allTrue (n : ℕ) : Assignment n := fun _ => true

def unitFormula (n : ℕ) : Formula := assignmentUnits (allTrue n)

theorem unitFormula_length (n : ℕ) : (unitFormula n).length = n := by
  simp [unitFormula, assignmentUnits]

theorem unitFormula_variablesBelow (n : ℕ) : VariablesBelow n (unitFormula n) := by
  intro c hc l hl
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
  simp only [List.mem_singleton] at hl
  subst l
  exact i.isLt

theorem unitFormula_eval_iff {n : ℕ} (a : Assignment n) :
    evalFormula (extendAssignment a) (unitFormula n) = true ↔ a = allTrue n := by
  rw [unitFormula, eval_assignmentUnits_iff]
  simp only [extendAssignment_fin]
  exact funext_iff.symm

theorem unitFormula_satisfiable (n : ℕ) : Satisfiable (unitFormula n) :=
  ⟨extendAssignment (allTrue n), (unitFormula_eval_iff (allTrue n)).mpr rfl⟩

/-- The full interpolation sum collapses to its single satisfying assignment. -/
theorem unitFormula_characteristic (n : ℕ) :
    verifierCharacteristic n (unitFormula n) = fullMonomial n := by
  classical
  unfold verifierCharacteristic interpolate Step4Compiler.chi_phi
  rw [Finset.sum_eq_single (allTrue n)]
  · rw [if_pos ((unitFormula_eval_iff (allTrue n)).mpr rfl)]
    simp [Step4Compiler.boolMonomial, allTrue, fullMonomial]
  · intro a _ hne
    rw [if_neg (fun h => hne ((unitFormula_eval_iff a).mp h))]
  · simp

/-- A straight-line product program: read each variable once, multiply into `1`. -/
def productProgram (n : ℕ) : List (Fin n) := List.finRange n

noncomputable def runProductProgram {n : ℕ} : List (Fin n) → Poly n
  | [] => 1
  | i :: rest => X i * runProductProgram rest

theorem runProductProgram_eq_prod {n : ℕ} (program : List (Fin n)) :
    runProductProgram program = (program.map fun i => (X i : Poly n)).prod := by
  induction program with
  | nil => rfl
  | cons i rest ih => simp [runProductProgram, ih]

/-- The operational definition performs one multiplication per instruction. -/
def multiplicationCount {n : ℕ} : List (Fin n) → ℕ
  | [] => 0
  | _ :: rest => multiplicationCount rest + 1

theorem multiplicationCount_eq_length {n : ℕ} (program : List (Fin n)) :
    multiplicationCount program = program.length := by
  induction program with
  | nil => rfl
  | cons i rest ih => simp [multiplicationCount, ih]

theorem productProgram_size (n : ℕ) :
    (productProgram n).length = n ∧ multiplicationCount (productProgram n) = n := by
  simp [multiplicationCount_eq_length, productProgram]

theorem productProgram_correct (n : ℕ) :
    runProductProgram (productProgram n) = verifierCharacteristic n (unitFormula n) := by
  rw [unitFormula_characteristic, runProductProgram_eq_prod]
  exact (Fin.prod_univ_def (fun i : Fin n => (X i : Poly n))).symm

/-- An explicit identity minor for the same new characteristic target. -/
theorem characteristic_coefficient_identity {n : ℕ} (S T : Finset (Fin n)) :
    coeff (complementaryColumn S)
        (iterDerivList T.toList (verifierCharacteristic n (unitFormula n))) =
      if S = T then 1 else 0 := by
  rw [unitFormula_characteristic]
  exact GodMoveMonomialMinor.coefficient_identity S T

theorem choose_le_characteristic_strict_rank (n k ell : ℕ) :
    Nat.choose n k ≤ mlBlockedSpdpRank (discreteBlocks n) k ell
      (verifierCharacteristic n (unitFormula n)) := by
  rw [unitFormula_characteristic]
  exact GodMoveMonomialMinor.choose_le_strict_rank n k ell

theorem choose_le_characteristic_inclusive_rank (n k ell : ℕ) :
    Nat.choose n k ≤ mlBlockedSpdpRankInc (discreteBlocks n) k ell
      (verifierCharacteristic n (unitFormula n)) := by
  rw [unitFormula_characteristic]
  exact GodMoveMonomialMinor.choose_le_inclusive_rank n k ell

/-- Any finite common span retaining these rows must pay the binomial budget.
Finiteness is explicit because `finrank` alone is not a dimension bound for
an infinite-dimensional polynomial subspace. -/
theorem choose_le_commonSpan_finrank (n k ell : ℕ)
    (W : Submodule ℚ (Poly n)) [FiniteDimensional ℚ W]
    (hW : mlBlockedSpdpSubspace (discreteBlocks n) k ell
      (verifierCharacteristic n (unitFormula n)) ≤ W) :
    Nat.choose n k ≤ Module.finrank ℚ W :=
  (choose_le_characteristic_strict_rank n k ell).trans (Submodule.finrank_mono hW)

/-- At logarithmic derivative order the same target exceeds each fixed power. -/
theorem npow_lt_characteristic_strict_rank (n d ell : ℕ)
    (hn : 2 ^ (max 20 (4 * (d + 1))) ≤ n) :
    n ^ d < mlBlockedSpdpRank (discreteBlocks n) (Nat.log 2 n) ell
      (verifierCharacteristic n (unitFormula n)) := by
  rw [unitFormula_characteristic]
  exact GodMoveMonomialMinor.npow_lt_strict_rank n d ell hn

theorem npow_lt_commonSpan_finrank (n d ell : ℕ)
    (hn : 2 ^ (max 20 (4 * (d + 1))) ≤ n)
    (W : Submodule ℚ (Poly n)) [FiniteDimensional ℚ W]
    (hW : mlBlockedSpdpSubspace (discreteBlocks n) (Nat.log 2 n) ell
      (verifierCharacteristic n (unitFormula n)) ≤ W) :
    n ^ d < Module.finrank ℚ W :=
  (GodMoveMonomialMinor.npow_lt_choose_log n d hn).trans_le
    (choose_le_commonSpan_finrank n (Nat.log 2 n) ell W hW)

/-- A uniform eventual polynomial bound on this target family is false,
without any machine or SAT-decider premise. -/
theorem no_eventual_polynomial_characteristic_strict_bound :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0,
      mlBlockedSpdpRank (discreteBlocks n) (Nat.log 2 n) 0
        (verifierCharacteristic n (unitFormula n)) ≤ C * n ^ d := by
  simpa only [unitFormula_characteristic] using
    GodMoveMonomialMinor.no_eventual_polynomial_strict_bound

theorem no_eventual_polynomial_characteristic_inclusive_bound :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0,
      mlBlockedSpdpRankInc (discreteBlocks n) (Nat.log 2 n) 0
        (verifierCharacteristic n (unitFormula n)) ≤ C * n ^ d := by
  simpa only [unitFormula_characteristic] using
    GodMoveMonomialMinor.no_eventual_polynomial_inclusive_bound

/-- The faithful query handshake inherits this lower bound for any SAT decider,
irrespective of its running time. This is not a source-side upper bound. -/
theorem choose_le_machineQuery_strict_rank (n k ell : ℕ)
    (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T) :
    Nat.choose n k ≤ mlBlockedSpdpRank (discreteBlocks n) k ell
      (machineQueryPolynomial (n := n) M T (unitFormula n)) := by
  rw [machineQueryPolynomial_eq_verifierCharacteristic M T hD _
    (unitFormula_variablesBelow n)]
  exact choose_le_characteristic_strict_rank n k ell

end GodMoveUnitCharacteristic

#print axioms GodMoveUnitCharacteristic.unitFormula_characteristic
#print axioms GodMoveUnitCharacteristic.productProgram_correct
#print axioms GodMoveUnitCharacteristic.productProgram_size
#print axioms GodMoveUnitCharacteristic.characteristic_coefficient_identity
#print axioms GodMoveUnitCharacteristic.choose_le_characteristic_strict_rank
#print axioms GodMoveUnitCharacteristic.choose_le_characteristic_inclusive_rank
#print axioms GodMoveUnitCharacteristic.choose_le_commonSpan_finrank
#print axioms GodMoveUnitCharacteristic.npow_lt_characteristic_strict_rank
#print axioms GodMoveUnitCharacteristic.npow_lt_commonSpan_finrank
#print axioms GodMoveUnitCharacteristic.no_eventual_polynomial_characteristic_strict_bound
#print axioms GodMoveUnitCharacteristic.no_eventual_polynomial_characteristic_inclusive_bound
#print axioms GodMoveUnitCharacteristic.choose_le_machineQuery_strict_rank
