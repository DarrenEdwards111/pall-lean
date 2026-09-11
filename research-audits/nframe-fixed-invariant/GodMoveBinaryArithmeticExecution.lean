import GodMoveBinaryFractionNormalize
import GodMoveBinaryMultiply
import GodMoveBooleanExecutionCost

/-!
# Executing the normalization circuit with counted wire traversal

This joins the actual emitted normalization gates to the finite Boolean/list
evaluator and materializes both result words. Correctness refers to the
canonical components of the actual normalized rational; the counter includes
every executed wire scan, store append and output read in that evaluator.

The count is for evaluation after the code and truth tables are available.
Circuit generation, translation, native allocation and a `ComposableMachine`
implementation are not included. The full cached projection builder has not
yet been replaced by this binary backend, and no SAT rank bound is asserted.
-/

namespace GodMoveBinaryArithmeticExecution

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open GodMoveBinaryAdder GodMoveSignedBinary GodMoveBinaryMultiply
open GodMoveBinaryFractionNormalize GodMoveRationalPrimitiveBounds
open GodMoveBooleanExecutionCost

/-- The counter belongs to the evaluator call; the executable code generator
and truth-table conversion are outside that counter. -/
def evaluateNormalization {n : ℕ} (inputs vals : List Bool) (xs ys : List ℕ) :
    Execution (List Bool × List Bool) :=
  let code := normalizeWords (n := n) vals.length xs ys
  executePair inputs vals (code.1.map lowerGate) code.2.1 code.2.2

theorem evaluateNormalization_canonical {n : ℕ} (inputs vals : List Bool)
    (xs ys : List ℕ) (hlen : xs.length = ys.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length)
    (f : RawFraction) (hnum : wordValue vals xs = f.numerator.natAbs)
    (hden : wordValue vals ys = f.denominator) :
    bitsValue (evaluateNormalization (n := n) inputs vals xs ys).value.1 =
        f.normalize.num.natAbs ∧
      bitsValue (evaluateNormalization (n := n) inputs vals xs ys).value.2 =
        f.normalize.den := by
  have h := normalizeWords_canonical (n := n) (fun i => inputs.getD i.val false)
    vals xs ys hlen hx hy f hnum hden
  simpa only [evaluateNormalization, executePair, collectWord_value,
    bitsValue_readWord, execute_lower_value] using h

theorem evaluateNormalization_decoded {n : ℕ} (inputs vals : List Bool)
    (xs ys : List ℕ) (hlen : xs.length = ys.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length)
    (f : RawFraction) (hnum : wordValue vals xs = f.numerator.natAbs)
    (hden : wordValue vals ys = f.denominator) :
    ((f.numerator.sign : ℚ) *
        bitsValue (evaluateNormalization (n := n) inputs vals xs ys).value.1) /
      bitsValue (evaluateNormalization (n := n) inputs vals xs ys).value.2 = f.normalize := by
  have h := normalizeWords_decoded (n := n) (fun i => inputs.getD i.val false)
    vals xs ys hlen hx hy f hnum hden
  simpa only [evaluateNormalization, executePair, collectWord_value,
    bitsValue_readWord, execute_lower_value] using h

/-- A concrete polynomial in word width and the already stored input/wire
lengths, obtained from the actual circuit gate count and evaluator counter. -/
def normalizationSteps (w inputLength storeLength : ℕ) : ℕ :=
  7 * (96 * (w + 1) ^ 3) * (inputLength + storeLength + 96 * (w + 1) ^ 3 + 1) +
    (2 * w) * (storeLength + 96 * (w + 1) ^ 3 + 2) + 1

theorem evaluateNormalization_steps_le {n : ℕ} (inputs vals : List Bool)
    (xs ys : List ℕ) (hlen : xs.length = ys.length) :
    (evaluateNormalization (n := n) inputs vals xs ys).steps ≤
      normalizationSteps xs.length inputs.length vals.length := by
  have hl := normalizeWords_lengths (n := n) vals.length xs ys hlen
  apply executePair_lower_steps_le inputs vals _ _ _ (96 * (xs.length + 1) ^ 3)
    (2 * xs.length) (normalizeWords_gate_count _ _ _ hlen)
  rw [hl.1, hl.2]
  omega

theorem normalizationSteps_le_sixth_power (w I V : ℕ) :
    normalizationSteps w I V ≤ 100000 * (I + V + w + 1) ^ 6 := by
  let S := I + V + w + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hw : w + 1 ≤ S := by dsimp [S]; omega
  have hi : I + V + 1 ≤ S := by dsimp [S]; omega
  have h3 : S ≤ S ^ 3 := by
    calc S = S ^ 1 := by simp
         _ ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide)
  have h4 : S ^ 4 ≤ S ^ 6 := Nat.pow_le_pow_right hS (by decide)
  have hb : 96 * (w + 1) ^ 3 ≤ 96 * S ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw _)
  have hinner : I + V + 96 * (w + 1) ^ 3 + 1 ≤ 97 * S ^ 3 := by omega
  have houter : V + 96 * (w + 1) ^ 3 + 2 ≤ 98 * S ^ 3 := by omega
  have hfirst : 7 * (96 * (w + 1) ^ 3) *
      (I + V + 96 * (w + 1) ^ 3 + 1) ≤ 65184 * S ^ 6 := by
    calc
      _ ≤ (7 * (96 * S ^ 3)) * (97 * S ^ 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hb) hinner
      _ = _ := by ring
  have hsecond : 2 * w * (V + 96 * (w + 1) ^ 3 + 2) ≤ 196 * S ^ 6 := by
    calc
      _ ≤ (2 * S) * (98 * S ^ 3) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega : w ≤ S)) houter
      _ = 196 * S ^ 4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h4
  have h6 : 1 ≤ S ^ 6 := Nat.one_le_pow _ _ hS
  change normalizationSteps w I V ≤ 100000 * S ^ 6
  unfold normalizationSteps
  omega

/-- Correct canonical result and proved polynomial traversal count for the
same execution, with all width and representation premises exposed. -/
theorem evaluateNormalization_correct_and_cost {n : ℕ} (inputs vals : List Bool)
    (xs ys : List ℕ) (hlen : xs.length = ys.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length)
    (f : RawFraction) (hnum : wordValue vals xs = f.numerator.natAbs)
    (hden : wordValue vals ys = f.denominator) :
    (((f.numerator.sign : ℚ) *
        bitsValue (evaluateNormalization (n := n) inputs vals xs ys).value.1) /
      bitsValue (evaluateNormalization (n := n) inputs vals xs ys).value.2 = f.normalize) ∧
    (evaluateNormalization (n := n) inputs vals xs ys).steps ≤
      100000 * (inputs.length + vals.length + xs.length + 1) ^ 6 :=
  ⟨evaluateNormalization_decoded inputs vals xs ys hlen hx hy f hnum hden,
    (evaluateNormalization_steps_le inputs vals xs ys hlen).trans
      (normalizationSteps_le_sixth_power _ _ _)⟩

end GodMoveBinaryArithmeticExecution

#print axioms GodMoveBinaryArithmeticExecution.evaluateNormalization_canonical
#print axioms GodMoveBinaryArithmeticExecution.evaluateNormalization_decoded
#print axioms GodMoveBinaryArithmeticExecution.evaluateNormalization_steps_le
#print axioms GodMoveBinaryArithmeticExecution.normalizationSteps_le_sixth_power
#print axioms GodMoveBinaryArithmeticExecution.evaluateNormalization_correct_and_cost
