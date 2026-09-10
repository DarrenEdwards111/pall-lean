import GodMoveUnitCharacteristic
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameCircuitUpgrade

/-!
# The characteristic-rank obstruction for actual Boolean circuits

Compile the full conjunction through the repository's verified tree-to-CGate
compiler. The resulting circuit has exactly `2*n+1` gates and its canonical
Boolean characteristic is the unit-CNF characteristic, hence `prod_i X_i`.
The actual strict and inclusive SPDP ranks at discrete blocks, logarithmic
derivative order and zero shift have no eventual polynomial upper bound in
the input-variable count plus this circuit's gate count.

This refutes a generic gate-count-to-characteristic-rank upper bound at these
specific parameters. It does not refute a theorem with an additional premise
of a globally correct polynomial-time SAT decider, nor rule out other dynamic
invariants or parameter choices. Circuit size alone cannot supply the proposed
rank bound, even when Boolean semantics and characteristic equality are exact.
-/

namespace GodMoveCircuitRankObstruction

open GodMoveBooleanInterpolation GodMovePinnedSATQueries
open GodMoveFaithfulHandshake GodMoveUnitCharacteristic
open GodMoveMonomialMinor (discreteBlocks fullMonomial)
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer CookLevinReduction

/-- The existing verified compiler, applied to an explicit conjunction tree. -/
def unitCircuit (n : ℕ) : List (CGate n) :=
  compile 0 (andVars (List.finRange n))

theorem unitCircuit_length (n : ℕ) : (unitCircuit n).length = 2 * n + 1 := by
  simp [unitCircuit, compile_length, volume_andVars]

private theorem fold_and_eq_true_iff {n : ℕ} (is : List (Fin n)) (a : Assignment n) :
    is.foldr (fun i acc => a i && acc) true = true ↔ ∀ i ∈ is, a i = true := by
  induction is with
  | nil => simp
  | cons i is ih => simp [ih]

theorem unitCircuit_output_eq_true_iff {n : ℕ} (a : Assignment n) :
    output (unitCircuit n) a = true ↔ a = allTrue n := by
  rw [show output (unitCircuit n) a = eval (andVars (List.finRange n)) a from
    compile_computes _ a]
  rw [eval_andVars, fold_and_eq_true_iff]
  simp only [List.mem_finRange, forall_true_left]
  exact funext_iff.symm

/-- Actual CGate evaluation computes the signed-CNF verifier on this family. -/
theorem unitCircuit_computes (n : ℕ) :
    computes (unitCircuit n)
      (fun a => evalFormula (extendAssignment a) (unitFormula n)) := by
  intro a
  apply Bool.eq_iff_iff.mpr
  exact (unitCircuit_output_eq_true_iff a).trans (unitFormula_eval_iff a).symm

/-- The canonical polynomial of the actual circuit output is the target. -/
theorem unitCircuit_characteristic (n : ℕ) :
    interpolate (output (unitCircuit n)) = verifierCharacteristic n (unitFormula n) :=
  interpolate_congr (unitCircuit_computes n)

theorem unitCircuit_characteristic_eq_fullMonomial (n : ℕ) :
    interpolate (output (unitCircuit n)) = fullMonomial n := by
  rw [unitCircuit_characteristic, unitFormula_characteristic]

theorem choose_le_unitCircuit_strict_rank (n k ell : ℕ) :
    Nat.choose n k ≤ mlBlockedSpdpRank (discreteBlocks n) k ell
      (interpolate (output (unitCircuit n))) := by
  rw [unitCircuit_characteristic]
  exact choose_le_characteristic_strict_rank n k ell

theorem choose_le_unitCircuit_inclusive_rank (n k ell : ℕ) :
    Nat.choose n k ≤ mlBlockedSpdpRankInc (discreteBlocks n) k ell
      (interpolate (output (unitCircuit n))) := by
  rw [unitCircuit_characteristic]
  exact choose_le_characteristic_inclusive_rank n k ell

/-- Even the combined number of inputs and gates does not polynomially bound
the strict characteristic rank for this linear-size family. -/
theorem no_eventual_polynomial_unitCircuit_strict_bound :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0,
      mlBlockedSpdpRank (discreteBlocks n) (Nat.log 2 n) 0
        (interpolate (output (unitCircuit n))) ≤
          C * (n + (unitCircuit n).length + 1) ^ d := by
  rintro ⟨C, d, n0, h⟩
  apply no_eventual_polynomial_characteristic_strict_bound
  refine ⟨C * 5 ^ d, d, max n0 1, ?_⟩
  intro n hn
  have hn0 : n0 ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hsize : n + (unitCircuit n).length + 1 ≤ 5 * n := by
    rw [unitCircuit_length]
    omega
  have hr := h n hn0
  rw [unitCircuit_characteristic] at hr
  calc
    _ ≤ C * (n + (unitCircuit n).length + 1) ^ d := hr
    _ ≤ C * (5 * n) ^ d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hsize d)
    _ = (C * 5 ^ d) * n ^ d := by rw [mul_pow, mul_assoc]

theorem no_eventual_polynomial_unitCircuit_inclusive_bound :
    ¬ ∃ C d n0 : ℕ, ∀ n ≥ n0,
      mlBlockedSpdpRankInc (discreteBlocks n) (Nat.log 2 n) 0
        (interpolate (output (unitCircuit n))) ≤
          C * (n + (unitCircuit n).length + 1) ^ d := by
  rintro ⟨C, d, n0, h⟩
  apply no_eventual_polynomial_characteristic_inclusive_bound
  refine ⟨C * 5 ^ d, d, max n0 1, ?_⟩
  intro n hn
  have hn0 : n0 ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hsize : n + (unitCircuit n).length + 1 ≤ 5 * n := by
    rw [unitCircuit_length]
    omega
  have hr := h n hn0
  rw [unitCircuit_characteristic] at hr
  calc
    _ ≤ C * (n + (unitCircuit n).length + 1) ^ d := hr
    _ ≤ C * (5 * n) ^ d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hsize d)
    _ = (C * 5 ^ d) * n ^ d := by rw [mul_pow, mul_assoc]

/-- No polynomial in input count and actual CGate count uniformly bounds this
strict canonical-characteristic rank for arbitrary circuits. -/
theorem no_polynomial_circuit_strict_bound :
    ¬ ∃ C d : ℕ, ∀ n (c : List (CGate n)),
      mlBlockedSpdpRank (discreteBlocks n) (Nat.log 2 n) 0
        (interpolate (output c)) ≤ C * (n + c.length + 1) ^ d := by
  rintro ⟨C, d, h⟩
  exact no_eventual_polynomial_unitCircuit_strict_bound
    ⟨C, d, 0, fun n _ => h n (unitCircuit n)⟩

theorem no_polynomial_circuit_inclusive_bound :
    ¬ ∃ C d : ℕ, ∀ n (c : List (CGate n)),
      mlBlockedSpdpRankInc (discreteBlocks n) (Nat.log 2 n) 0
        (interpolate (output c)) ≤ C * (n + c.length + 1) ^ d := by
  rintro ⟨C, d, h⟩
  exact no_eventual_polynomial_unitCircuit_inclusive_bound
    ⟨C, d, 0, fun n _ => h n (unitCircuit n)⟩

end GodMoveCircuitRankObstruction

#print axioms GodMoveCircuitRankObstruction.unitCircuit_length
#print axioms GodMoveCircuitRankObstruction.unitCircuit_computes
#print axioms GodMoveCircuitRankObstruction.unitCircuit_characteristic
#print axioms GodMoveCircuitRankObstruction.unitCircuit_characteristic_eq_fullMonomial
#print axioms GodMoveCircuitRankObstruction.choose_le_unitCircuit_strict_rank
#print axioms GodMoveCircuitRankObstruction.choose_le_unitCircuit_inclusive_rank
#print axioms GodMoveCircuitRankObstruction.no_eventual_polynomial_unitCircuit_strict_bound
#print axioms GodMoveCircuitRankObstruction.no_eventual_polynomial_unitCircuit_inclusive_bound
#print axioms GodMoveCircuitRankObstruction.no_polynomial_circuit_strict_bound
#print axioms GodMoveCircuitRankObstruction.no_polynomial_circuit_inclusive_bound
