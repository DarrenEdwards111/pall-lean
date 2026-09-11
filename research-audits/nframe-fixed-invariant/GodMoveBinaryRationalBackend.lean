import GodMoveBinaryScalarExecution
import GodMoveBinaryRationalAdd
import GodMoveBinaryRationalDivide

/-!
# A concrete scalar backend for materialized binary rationals

Dispatch selects one of the four proved Boolean circuits. Operands are packed
from their actual sign and magnitude lists, and the evaluator materializes all
three result fields from the executed wire store. Native rational operations
occur only in the mathematical specification.

The counter measures the explicit evaluator's Boolean/list traversals. Input
packing/padding, circuit generation, truth-table lowering, instrumentation
counter arithmetic, native allocation, and physical-machine compilation are
outside that counter. This is not the complete cached builder runtime bound.
-/

namespace GodMoveBinaryRationalBackend

open GodMoveBinaryScalarExecution GodMoveRationalWireEncoding GodMoveBooleanExecutionCost
open GodMoveBinaryRationalAdd GodMoveBinaryRationalMultiply GodMoveBinaryRationalDivide
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

inductive Op where
  | add | sub | mul | div
  deriving Repr, DecidableEq

/-- Rational operations specify the backend result; they do not compute its bits. -/
def Op.value : Op → ℚ → ℚ → ℚ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => x / y

def compile {n : ℕ} (op : Op) (start : ℕ) (x y : FractionRefs) :
    List (CGate n) × FractionRefs :=
  match op with
  | .add => addFractions start x y
  | .sub => subtractFractions start x y
  | .mul => multiplyFractions start x y
  | .div => divideFractions start x y

def outputWidth : Op → ℕ → ℕ
  | .add, w => 2 * w + 1
  | .sub, w => 2 * w + 1
  | .mul, w => 2 * w
  | .div, w => 2 * w

theorem compile_width {n : ℕ} (op : Op) (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    Width (compile (n := n) op start x y).2 (outputWidth op w) := by
  cases op with
  | add => exact addFractions_width start x y w hx hy
  | sub => exact subtractFractions_width start x y w hx hy
  | mul => exact multiplyFractions_width start x y w hx hy
  | div => exact divideFractions_width start x y w hx hy

theorem compile_gate_count {n : ℕ} (op : Op) (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    (compile (n := n) op start x y).1.length ≤ 2048 * (w + 1) ^ 3 := by
  cases op with
  | add => exact (addFractions_gate_count start x y w hx hy).trans (by omega)
  | sub => exact (subtractFractions_gate_count start x y w hx hy).trans (by omega)
  | mul => exact (multiplyFractions_gate_count start x y w hx hy).trans (by omega)
  | div => exact (divideFractions_gate_count start x y w hx hy).trans (by omega)

theorem compile_output_bits {n : ℕ} (op : Op) (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    (compile (n := n) op start x y).2.numerator.length +
      (compile (n := n) op start x y).2.denominator.length + 1 ≤ 4 * w + 3 := by
  have h := compile_width (n := n) op start x y w hx hy
  rw [h.1, h.2]
  cases op <;> simp only [outputWidth] <;> omega

theorem compile_valid {n : ℕ} (op : Op) (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    Valid (compile (n := n) op start x y).2 (start + (compile (n := n) op start x y).1.length) := by
  cases op with
  | add => exact addFractions_valid start x y w hx hy
  | sub => exact subtractFractions_valid start x y w hx hy
  | mul => exact multiplyFractions_valid start x y w hx hy
  | div => exact divideFractions_valid start x y w hx hy

theorem compile_represents {n : ℕ} (op : Op) (a : Fin n → Bool) (vals : List Bool)
    (x y : FractionRefs) (q r : ℚ) (w : ℕ)
    (hxw : Width x w) (hyw : Width y w)
    (hxv : Valid x vals.length) (hyv : Valid y vals.length)
    (hx : Represents vals x q) (hy : Represents vals y r) :
    Represents (runFrom a vals (compile op vals.length x y).1)
      (compile (n := n) op vals.length x y).2 (op.value q r) := by
  cases op with
  | add => exact addFractions_represents a vals x y q r w hxw hyw hxv hyv hx hy
  | sub => exact subtractFractions_represents a vals x y q r w hxw hyw hxv hyv hx hy
  | mul => exact multiplyFractions_represents a vals x y q r w hxw hyw hxv hyv hx hy
  | div => exact divideFractions_represents a vals x y q r w hxw hyw hxv hyv hx hy

/-- The width is computed from stored list lengths, not the rational denotations. -/
def inputWidth (x y : FractionBits) : ℕ :=
  x.numerator.length + x.denominator.length + y.numerator.length + y.denominator.length + 1

theorem inputWidth_bounds (x y : FractionBits) :
    x.numerator.length ≤ inputWidth x y ∧ x.denominator.length ≤ inputWidth x y ∧
      y.numerator.length ≤ inputWidth x y ∧ y.denominator.length ≤ inputWidth x y := by
  unfold inputWidth
  omega

def inputStore (x y : FractionBits) : List Bool :=
  pack (inputWidth x y) x ++ pack (inputWidth x y) y

def refsX (x y : FractionBits) : FractionRefs := packedRefs 0 (inputWidth x y)
def refsY (x y : FractionBits) : FractionRefs :=
  packedRefs (2 * inputWidth x y + 1) (inputWidth x y)

theorem inputStore_length (x y : FractionBits) :
    (inputStore x y).length = 4 * inputWidth x y + 2 := by
  have h := inputWidth_bounds x y
  simp only [inputStore, List.length_append, pack_length _ _ h.1 h.2.1,
    pack_length _ _ h.2.2.1 h.2.2.2]
  omega

theorem refs_width (x y : FractionBits) :
    Width (refsX x y) (inputWidth x y) ∧ Width (refsY x y) (inputWidth x y) :=
  ⟨packedRefs_width _ _, packedRefs_width _ _⟩

theorem refs_valid (x y : FractionBits) :
    Valid (refsX x y) (inputStore x y).length ∧
      Valid (refsY x y) (inputStore x y).length := by
  have hx := packedRefs_valid 0 (inputWidth x y)
  have hy := packedRefs_valid (2 * inputWidth x y + 1) (inputWidth x y)
  exact ⟨hx.mono (by rw [inputStore_length]; omega),
    hy.mono (by rw [inputStore_length]; omega)⟩

theorem inputStore_represents (x y : FractionBits) (q r : ℚ)
    (hx : x.Represents q) (hy : y.Represents r) :
    Represents (inputStore x y) (refsX x y) q ∧
      Represents (inputStore x y) (refsY x y) r := by
  have h := inputWidth_bounds x y
  have hX := packedRefs_represents [] (pack (inputWidth x y) y) x q (inputWidth x y) h.1 h.2.1 hx
  have hY := packedRefs_represents (pack (inputWidth x y) x) [] y r (inputWidth x y)
    h.2.2.1 h.2.2.2 hy
  constructor
  · simpa only [List.nil_append, List.length_nil, inputStore, refsX] using hX
  · simpa only [List.append_nil, pack_length _ _ h.1 h.2.1, inputStore, refsY] using hY

/-- Every result bit, including its sign, is obtained from the executed circuit. -/
def evaluate (op : Op) (x y : FractionBits) : Execution FractionBits :=
  let vals := inputStore x y
  let code := compile (n := 0) op vals.length (refsX x y) (refsY x y)
  executeFraction [] vals code.1 code.2

theorem evaluate_represents (op : Op) (x y : FractionBits) (q r : ℚ)
    (hx : x.Represents q) (hy : y.Represents r) :
    (evaluate op x y).value.Represents (op.value q r) := by
  have hr := inputStore_represents x y q r hx hy
  have hw := refs_width x y
  have hv := refs_valid x y
  apply executeFraction_represents
  exact compile_represents (n := 0) op (fun i => [].getD i.val false) (inputStore x y)
    (refsX x y) (refsY x y) q r (inputWidth x y) hw.1 hw.2 hv.1 hv.2 hr.1 hr.2

theorem evaluate_value (op : Op) (x y : FractionBits) (q r : ℚ)
    (hx : x.Represents q) (hy : y.Represents r) :
    (evaluate op x y).value.value = op.value q r :=
  (evaluate_represents op x y q r hx hy).value_eq

/-- Explicit traversal bound after the store, code and truth tables are available. -/
def traversalSteps (w : ℕ) : ℕ :=
  7 * (2048 * (w + 1) ^ 3) * (4 * w + 2 + 2048 * (w + 1) ^ 3 + 1) +
    (4 * w + 3) * (4 * w + 2 + 2048 * (w + 1) ^ 3 + 2) + 1

theorem evaluate_steps_le (op : Op) (x y : FractionBits) :
    (evaluate op x y).steps ≤ traversalSteps (inputWidth x y) := by
  have hw := refs_width x y
  have h := executeFraction_steps_le (n := 0) [] (inputStore x y)
    (compile (n := 0) op (inputStore x y).length (refsX x y) (refsY x y)).1
    (compile (n := 0) op (inputStore x y).length (refsX x y) (refsY x y)).2
    (2048 * (inputWidth x y + 1) ^ 3) (4 * inputWidth x y + 3)
    (compile_gate_count (n := 0) op _ _ _ _ hw.1 hw.2) (compile_output_bits (n := 0) op _ _ _ _ hw.1 hw.2)
  simpa only [evaluate, traversalSteps, List.length_nil, zero_add, inputStore_length] using h

theorem traversalSteps_le_sixth_power (w : ℕ) :
    traversalSteps w ≤ 40000000 * (w + 1) ^ 6 := by
  let s := w + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have h3 : s ≤ s ^ 3 := by
    calc s = s ^ 1 := by simp
         _ ≤ _ := Nat.pow_le_pow_right hs (by decide)
  have h4 : s ^ 4 ≤ s ^ 6 := Nat.pow_le_pow_right hs (by decide)
  have hin : 4 * w + 2 + 2048 * s ^ 3 + 1 ≤ 2052 * s ^ 3 := by dsimp [s] at *; omega
  have hout : 4 * w + 2 + 2048 * s ^ 3 + 2 ≤ 2052 * s ^ 3 := by dsimp [s] at *; omega
  have hfirst : 7 * (2048 * s ^ 3) * (4 * w + 2 + 2048 * s ^ 3 + 1) ≤
      29417472 * s ^ 6 := by
    calc _ ≤ (7 * (2048 * s ^ 3)) * (2052 * s ^ 3) := Nat.mul_le_mul_left _ hin
         _ = _ := by ring
  have hsecond : (4 * w + 3) * (4 * w + 2 + 2048 * s ^ 3 + 2) ≤ 8208 * s ^ 6 := by
    calc _ ≤ (4 * s) * (2052 * s ^ 3) := Nat.mul_le_mul (by dsimp [s]; omega) hout
         _ = 8208 * s ^ 4 := by ring
         _ ≤ _ := Nat.mul_le_mul_left _ h4
  have h6 : 1 ≤ s ^ 6 := Nat.one_le_pow _ _ hs
  change traversalSteps w ≤ 40000000 * s ^ 6
  unfold traversalSteps
  change 7 * (2048 * s ^ 3) * (4 * w + 2 + 2048 * s ^ 3 + 1) +
    (4 * w + 3) * (4 * w + 2 + 2048 * s ^ 3 + 2) + 1 ≤ _
  omega

/-- Canonical correctness and the actual evaluator counter concern one returned
execution result. Packing, lowering and circuit construction are not charged. -/
theorem evaluate_correct_and_cost (op : Op) (x y : FractionBits) (q r : ℚ)
    (hx : x.Represents q) (hy : y.Represents r) :
    (evaluate op x y).value.Represents (op.value q r) ∧
      (evaluate op x y).steps ≤ 40000000 * (inputWidth x y + 1) ^ 6 :=
  ⟨evaluate_represents op x y q r hx hy,
    (evaluate_steps_le op x y).trans (traversalSteps_le_sixth_power _)⟩

end GodMoveBinaryRationalBackend

#print axioms GodMoveBinaryRationalBackend.compile_represents
#print axioms GodMoveBinaryRationalBackend.compile_gate_count
#print axioms GodMoveBinaryRationalBackend.compile_output_bits
#print axioms GodMoveBinaryRationalBackend.inputStore_represents
#print axioms GodMoveBinaryRationalBackend.evaluate_represents
#print axioms GodMoveBinaryRationalBackend.evaluate_value
#print axioms GodMoveBinaryRationalBackend.evaluate_steps_le
#print axioms GodMoveBinaryRationalBackend.traversalSteps_le_sixth_power
#print axioms GodMoveBinaryRationalBackend.evaluate_correct_and_cost
