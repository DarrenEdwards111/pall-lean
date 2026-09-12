import GodMoveBinaryRationalCompileCost
import GodMoveRationalAddCompileCost
import GodMoveStoredScalarBackend

/-!
# Scalar execution with the actual rational generator in the counter

This endpoint substitutes the counted rational compilers into the stored
program backend. It prepares the operands once, generates their circuit,
serializes and decodes that circuit, executes it once, and reads the result.
The generated code and reference layout agree exactly with the preceding
canonical rational backend.

The counter is the shared-list/index traversal model. Converting function
closures into truth tables, instrumentation arithmetic, native allocation,
the adaptive builder, and a uniform tape-machine implementation are still
outside this theorem. In particular this is not a SAT derivative-rank bound.
-/

namespace GodMoveGeneratedScalarBackend

open GodMoveBooleanExecutionCost GodMoveBinaryScalarExecution
open GodMoveRationalWireEncoding GodMoveBinaryRationalBackend
open GodMoveBinaryPackingCost GodMoveStoredScalarBackend
open GodMoveBinaryRationalCompileCost GodMoveRationalAddCompileCost
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate runFrom)

/-- Dispatch executes one of the counted generators, including normalization. -/
def compileCounted {n : ℕ} (op : Op) (start : ℕ) (x y : FractionRefs) :
    Execution (List (CGate n) × FractionRefs) :=
  let generated := match op with
    | .add => addFractionsCounted start x y
    | .sub => subtractFractionsCounted start x y
    | .mul => multiplyFractionsCounted start x y
    | .div => divideFractionsCounted start x y
  ⟨generated.value, generated.steps + 1⟩

theorem compileCounted_value {n : ℕ} (op : Op) (start : ℕ) (x y : FractionRefs) :
    (compileCounted (n := n) op start x y).value = compile op start x y := by
  cases op <;> simp only [compileCounted, compile, addFractionsCounted_value,
    subtractFractionsCounted_value, multiplyFractionsCounted_value, divideFractionsCounted_value]

theorem compileCounted_steps_le {n : ℕ} (op : Op) (start : ℕ) (x y : FractionRefs)
    (w : ℕ) (hx : Width x w) (hy : Width y w) :
    (compileCounted (n := n) op start x y).steps ≤ 10000000 * (w + 1) ^ 5 := by
  have hp : 1 ≤ (w + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  cases op with
  | add =>
    have h := addFractionsCounted_steps_le (n := n) start x y w hx hy
    simp only [compileCounted]
    omega
  | sub =>
    have h := subtractFractionsCounted_steps_le (n := n) start x y w hx hy
    simp only [compileCounted]
    omega
  | mul =>
    have h := multiplyFractionsCounted_steps_le (n := n) start x y w hx hy
    simp only [compileCounted]
    omega
  | div =>
    have h := divideFractionsCounted_steps_le (n := n) start x y w hx hy
    simp only [compileCounted]
    omega

theorem compileCounted_represents {n : ℕ} (op : Op) (a : Fin n → Bool)
    (vals : List Bool) (x y : FractionRefs) (q r : ℚ) (w : ℕ)
    (hxw : Width x w) (hyw : Width y w)
    (hxv : Valid x vals.length) (hyv : Valid y vals.length)
    (hx : Represents vals x q) (hy : Represents vals y r) :
    Represents (runFrom a vals (compileCounted op vals.length x y).value.1)
      (compileCounted (n := n) op vals.length x y).value.2 (op.value q r) := by
  simp only [compileCounted_value]
  exact compile_represents op a vals x y q r w hxw hyw hxv hyv hx hy

/-- Every stage consumes the values actually returned by its predecessor. -/
def evaluateGenerated (op : Op) (x y : FractionBits) : Execution (Option FractionBits) :=
  let prep := prepareInputs x y
  let code := compileCounted (n := 0) op prep.value.start prep.value.left prep.value.right
  let result := executeStoredFraction [] prep.value.store code.value.1 code.value.2
  ⟨result.value, prep.steps + code.steps + result.steps + 1⟩

theorem evaluateGenerated_value (op : Op) (x y : FractionBits) :
    (evaluateGenerated op x y).value = some (evaluate op x y).value := by
  simp only [evaluateGenerated, compileCounted_value, executeStoredFraction_value,
    prepareInputs_value, originalPrepared, evaluate]

theorem evaluateGenerated_steps (op : Op) (x y : FractionBits) :
    (evaluateGenerated op x y).steps = (evaluateStored op x y).steps +
      (compileCounted (n := 0) op (inputStore x y).length (refsX x y) (refsY x y)).steps := by
  simp only [evaluateGenerated, evaluateStored, compileCounted_value,
    prepareInputs_value, originalPrepared]
  omega

theorem evaluateGenerated_represents (op : Op) (x y : FractionBits) (q r : ℚ)
    (hx : x.Represents q) (hy : y.Represents r) :
    ∃ result, (evaluateGenerated op x y).value = some result ∧
      result.Represents (op.value q r) := by
  exact ⟨(evaluate op x y).value, evaluateGenerated_value op x y,
    evaluate_represents op x y q r hx hy⟩

theorem evaluateGenerated_steps_le (op : Op) (x y : FractionBits) :
    (evaluateGenerated op x y).steps ≤ 210000000 * (inputWidth x y + 1) ^ 6 := by
  have hw := refs_width x y
  have hc := compileCounted_steps_le (n := 0) op (inputStore x y).length
    (refsX x y) (refsY x y) (inputWidth x y) hw.1 hw.2
  have he := (evaluateStored_steps_le op x y).trans (storedScalarSteps_le_sixth_power _)
  have h56 : (inputWidth x y + 1) ^ 5 ≤ (inputWidth x y + 1) ^ 6 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  rw [evaluateGenerated_steps]
  omega

theorem evaluateGenerated_correct_and_cost (op : Op) (x y : FractionBits) (q r : ℚ)
    (hx : x.Represents q) (hy : y.Represents r) :
    (∃ result, (evaluateGenerated op x y).value = some result ∧
      result.Represents (op.value q r)) ∧
    (evaluateGenerated op x y).steps ≤ 210000000 * (inputWidth x y + 1) ^ 6 :=
  ⟨evaluateGenerated_represents op x y q r hx hy, evaluateGenerated_steps_le op x y⟩

end GodMoveGeneratedScalarBackend

#print axioms GodMoveGeneratedScalarBackend.compileCounted_value
#print axioms GodMoveGeneratedScalarBackend.compileCounted_steps_le
#print axioms GodMoveGeneratedScalarBackend.compileCounted_represents
#print axioms GodMoveGeneratedScalarBackend.evaluateGenerated_value
#print axioms GodMoveGeneratedScalarBackend.evaluateGenerated_steps
#print axioms GodMoveGeneratedScalarBackend.evaluateGenerated_represents
#print axioms GodMoveGeneratedScalarBackend.evaluateGenerated_steps_le
#print axioms GodMoveGeneratedScalarBackend.evaluateGenerated_correct_and_cost
