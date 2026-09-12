import GodMoveStoredProgramExecution
import GodMoveBinaryPackingCost

/-!
# Rational scalar execution through an encoded Boolean program

The backend prepares the actual operand bits and reference layout, serializes
and decodes the generated instructions, executes the decoded program, and reads
the returned sign and magnitude words. Output collection uses an empty program
on the returned store, so the arithmetic circuit is executed only once.

The counter includes operand preparation, program-length preparation, bounded
unary serialization, decoding, evaluator traversals and output collection.
Circuit generation, conversion of gate closures to truth tables, counter
arithmetic and compilation of these routines into a tape machine remain outside
this traversal-model bound. No native rational computation supplies output bits.
-/

namespace GodMoveStoredScalarBackend

open GodMoveBooleanExecutionCost GodMoveBinaryScalarExecution
open GodMoveRationalWireEncoding GodMoveBinaryRationalBackend
open GodMoveBinaryPackingCost GodMoveStoredProgramExecution
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- Serialize, decode and execute once; collect only from the returned store. -/
def executeStoredFraction {n : ℕ} (inputs vals : List Bool)
    (code : List (CGate n)) (refs : FractionRefs) : Execution (Option FractionBits) :=
  let executed := executePrepared inputs vals (code.map lowerGate)
  match executed.value with
  | none => ⟨none, executed.steps + 1⟩
  | some store =>
      let result := executeFraction (n := 0) [] store [] refs
      ⟨some result.value, executed.steps + result.steps + 1⟩

theorem collect_after_execute_value {n : ℕ} (inputs vals : List Bool)
    (code : List (CGate n)) (refs : FractionRefs) :
    (executeFraction (n := 0) []
      (execute inputs vals (code.map lowerGate)).value [] refs).value =
        (executeFraction inputs vals code refs).value := by
  rfl

theorem executeStoredFraction_value {n : ℕ} (inputs vals : List Bool)
    (code : List (CGate n)) (refs : FractionRefs) :
    (executeStoredFraction inputs vals code refs).value =
      some (executeFraction inputs vals code refs).value := by
  simp only [executeStoredFraction, executePrepared_value, collect_after_execute_value]

theorem executeStoredFraction_steps {n : ℕ} (inputs vals : List Bool)
    (code : List (CGate n)) (refs : FractionRefs) :
    (executeStoredFraction inputs vals code refs).steps =
      (executePrepared inputs vals (code.map lowerGate)).steps +
        (executeFraction (n := 0) []
          (execute inputs vals (code.map lowerGate)).value [] refs).steps + 1 := by
  simp only [executeStoredFraction, executePrepared_value]

theorem executeStoredFraction_steps_le {n : ℕ} (inputs vals : List Bool)
    (code : List (CGate n)) (refs : FractionRefs) (G R : ℕ)
    (hg : code.length ≤ G)
    (hr : refs.numerator.length + refs.denominator.length + 1 ≤ R) :
    (executeStoredFraction inputs vals code refs).steps ≤
      32 * (inputs.length + vals.length + G + 4) ^ 2 +
        R * (vals.length + G + 2) + 2 := by
  have he := executePrepared_steps_le inputs vals (code.map lowerGate)
  have hc := executeFraction_steps_le (n := 0) []
    (execute inputs vals (code.map lowerGate)).value [] refs 0 R (by simp) hr
  simp only [List.length_map] at he
  simp only [List.length_nil, execute_value_length, List.length_map,
    Nat.zero_add, Nat.add_zero] at hc
  have he' : 32 * (inputs.length + vals.length + code.length + 4) ^ 2 ≤
      32 * (inputs.length + vals.length + G + 4) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hc' : R * (vals.length + code.length + 2) ≤ R * (vals.length + G + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  rw [executeStoredFraction_steps]
  omega

/-- Operand preparation is cached; its store and references supply this run. -/
def evaluateStored (op : Op) (x y : FractionBits) : Execution (Option FractionBits) :=
  let prep := prepareInputs x y
  let code := compile (n := 0) op prep.value.start prep.value.left prep.value.right
  let result := executeStoredFraction [] prep.value.store code.1 code.2
  ⟨result.value, prep.steps + result.steps + 1⟩

theorem evaluateStored_value (op : Op) (x y : FractionBits) :
    (evaluateStored op x y).value = some (evaluate op x y).value := by
  simp only [evaluateStored, executeStoredFraction_value, prepareInputs_value,
    originalPrepared, evaluate]

/-- Canonical signed components are the bits read from the decoded run. -/
theorem evaluateStored_represents (op : Op) (x y : FractionBits) (q r : ℚ)
    (hx : x.Represents q) (hy : y.Represents r) :
    ∃ result, (evaluateStored op x y).value = some result ∧
      result.Represents (op.value q r) := by
  exact ⟨(evaluate op x y).value, evaluateStored_value op x y,
    evaluate_represents op x y q r hx hy⟩

def storedScalarSteps (w : ℕ) : ℕ :=
  64 * (w + 1) + 32 * (4 * w + 2 + 2048 * (w + 1) ^ 3 + 4) ^ 2 +
    (4 * w + 3) * (4 * w + 2 + 2048 * (w + 1) ^ 3 + 2) + 3

theorem evaluateStored_steps_le (op : Op) (x y : FractionBits) :
    (evaluateStored op x y).steps ≤ storedScalarSteps (inputWidth x y) := by
  have hp := prepareInputs_steps_le x y
  have hw := refs_width x y
  have hg := compile_gate_count (n := 0) op (inputStore x y).length
    (refsX x y) (refsY x y) (inputWidth x y) hw.1 hw.2
  have hr := compile_output_bits (n := 0) op (inputStore x y).length
    (refsX x y) (refsY x y) (inputWidth x y) hw.1 hw.2
  have he := executeStoredFraction_steps_le [] (inputStore x y)
    (compile (n := 0) op (inputStore x y).length (refsX x y) (refsY x y)).1
    (compile (n := 0) op (inputStore x y).length (refsX x y) (refsY x y)).2
    (2048 * (inputWidth x y + 1) ^ 3) (4 * inputWidth x y + 3) hg hr
  simp only [List.length_nil, Nat.zero_add, inputStore_length] at he
  simp only [evaluateStored, prepareInputs_value, originalPrepared, storedScalarSteps,
    inputStore_length]
  omega

theorem storedScalarSteps_le_sixth_power (w : ℕ) :
    storedScalarSteps w ≤ 200000000 * (w + 1) ^ 6 := by
  let s := w + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have h13 : s ≤ s ^ 3 := by
    calc
      _ = s ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right hs (by decide)
  have h16 : s ≤ s ^ 6 := by
    calc
      _ = s ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right hs (by decide)
  have h46 : s ^ 4 ≤ s ^ 6 := Nat.pow_le_pow_right hs (by decide)
  have h06 : 1 ≤ s ^ 6 := one_le_pow₀ hs
  have hb : 4 * w + 2 + 2048 * s ^ 3 + 4 ≤ 2054 * s ^ 3 := by
    dsimp [s] at h13 ⊢
    omega
  have hb2 := Nat.pow_le_pow_left hb 2
  have hm : (4 * w + 3) * (4 * w + 2 + 2048 * s ^ 3 + 2) ≤
      (4 * s) * (2052 * s ^ 3) := by
    apply Nat.mul_le_mul
    · dsimp [s]; omega
    · dsimp [s] at h13 ⊢; omega
  have hp2 : (2054 * s ^ 3) ^ 2 = 4218916 * s ^ 6 := by ring
  have hp4 : (4 * s) * (2052 * s ^ 3) = 8208 * s ^ 4 := by ring
  rw [hp2] at hb2
  rw [hp4] at hm
  change 64 * s + 32 * (4 * w + 2 + 2048 * s ^ 3 + 4) ^ 2 +
    (4 * w + 3) * (4 * w + 2 + 2048 * s ^ 3 + 2) + 3 ≤ 200000000 * s ^ 6
  omega

theorem evaluateStored_correct_and_cost (op : Op) (x y : FractionBits) (q r : ℚ)
    (hx : x.Represents q) (hy : y.Represents r) :
    (∃ result, (evaluateStored op x y).value = some result ∧
      result.Represents (op.value q r)) ∧
    (evaluateStored op x y).steps ≤ 200000000 * (inputWidth x y + 1) ^ 6 := by
  exact ⟨evaluateStored_represents op x y q r hx hy,
    (evaluateStored_steps_le op x y).trans (storedScalarSteps_le_sixth_power _)⟩

end GodMoveStoredScalarBackend

#print axioms GodMoveStoredScalarBackend.executeStoredFraction_value
#print axioms GodMoveStoredScalarBackend.executeStoredFraction_steps_le
#print axioms GodMoveStoredScalarBackend.evaluateStored_value
#print axioms GodMoveStoredScalarBackend.evaluateStored_represents
#print axioms GodMoveStoredScalarBackend.evaluateStored_steps_le
#print axioms GodMoveStoredScalarBackend.storedScalarSteps_le_sixth_power
#print axioms GodMoveStoredScalarBackend.evaluateStored_correct_and_cost
