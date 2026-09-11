import GodMoveBinaryAdder

/-!
# Explicit traversal accounting for a Boolean circuit evaluator

The evaluator uses stored Boolean truth tables and explicit recursive wire
lookup and append programs. Its counter counts list/index traversal, Boolean
table selection and control steps. It includes repeated wire reads and the
copies made by appending to an immutable list; it assumes no constant-time
random access. Erasure agrees with the production `runFrom` evaluator.

This is an execution bound in the specified Boolean/list primitive model.
It does not bound translation of arbitrary Lean function closures, circuit
generation, native allocation or a compilation into `ComposableMachine`.
-/

namespace GodMoveBooleanExecutionCost

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open GodMoveBinaryAdder

structure Execution (α : Type*) where
  value : α
  steps : ℕ
  deriving Repr, DecidableEq

/-- Stored tables make all Boolean operations explicit finite data. -/
inductive Gate where
  | constant (value : Bool)
  | input (index : ℕ)
  | unary (onFalse onTrue : Bool) (index : ℕ)
  | binary (ff ft tf tt : Bool) (left right : ℕ)
  deriving Repr, DecidableEq

def lowerGate {n : ℕ} : CGate n → Gate
  | .cst b => .constant b
  | .var i => .input i.val
  | .un f i => .unary (f false) (f true) i
  | .bin f i j => .binary (f false false) (f false true) (f true false) (f true true) i j

/-- Each recursive branch visits one list/index cell; a missing reference
returns false, matching the production evaluator. -/
def readWire : List Bool → ℕ → Execution Bool
  | [], _ => ⟨false, 1⟩
  | b :: _, 0 => ⟨b, 1⟩
  | _ :: bs, i + 1 =>
    let r := readWire bs i
    ⟨r.value, r.steps + 1⟩

theorem readWire_value (bs : List Bool) (i : ℕ) :
    (readWire bs i).value = bs.getD i false := by
  induction bs generalizing i with
  | nil => simp [readWire]
  | cons b bs ih => cases i <;> simp [readWire, ih]

theorem readWire_steps_le (bs : List Bool) (i : ℕ) :
    (readWire bs i).steps ≤ bs.length + 1 := by
  induction bs generalizing i with
  | nil => simp [readWire]
  | cons b bs ih =>
    cases i with
    | zero => simp [readWire]
    | succ i => simpa only [readWire, List.length_cons] using Nat.succ_le_succ (ih i)

def appendBit : List Bool → Bool → Execution (List Bool)
  | [], b => ⟨[b], 1⟩
  | x :: xs, b =>
    let r := appendBit xs b
    ⟨x :: r.value, r.steps + 1⟩

theorem appendBit_value (bs : List Bool) (b : Bool) :
    (appendBit bs b).value = bs ++ [b] := by
  induction bs with
  | nil => rfl
  | cons x xs ih => simp [appendBit, ih]

theorem appendBit_steps (bs : List Bool) (b : Bool) :
    (appendBit bs b).steps = bs.length + 1 := by
  induction bs with
  | nil => rfl
  | cons x xs ih => simp [appendBit, ih]

/-- One opcode dispatch, all actual wire scans, and one/two Boolean selections
for unary/binary truth tables. -/
def executeGate (inputs vals : List Bool) : Gate → Execution Bool
  | .constant b => ⟨b, 1⟩
  | .input i =>
    let r := readWire inputs i
    ⟨r.value, r.steps + 1⟩
  | .unary f t i =>
    let r := readWire vals i
    ⟨if r.value then t else f, r.steps + 2⟩
  | .binary ff ft tf tt i j =>
    let x := readWire vals i
    let y := readWire vals j
    ⟨if x.value then (if y.value then tt else tf) else (if y.value then ft else ff),
      x.steps + y.steps + 3⟩

theorem executeGate_lower_value {n : ℕ} (inputs vals : List Bool) (g : CGate n) :
    (executeGate inputs vals (lowerGate g)).value =
      evalGate (fun i => inputs.getD i.val false) vals g := by
  cases g with
  | cst b => rfl
  | var i => exact readWire_value inputs i.val
  | un f i =>
    simp only [executeGate, lowerGate, evalGate, readWire_value]
    cases vals.getD i false <;> rfl
  | bin f i j =>
    simp only [executeGate, lowerGate, evalGate, readWire_value]
    cases vals.getD i false <;> cases vals.getD j false <;> rfl

theorem executeGate_steps_le (inputs vals : List Bool) (g : Gate) :
    (executeGate inputs vals g).steps ≤ 2 * (inputs.length + vals.length + 1) + 3 := by
  cases g with
  | constant b => simp [executeGate]
  | input i =>
    have h := readWire_steps_le inputs i
    simp only [executeGate]
    omega
  | unary f t i =>
    have h := readWire_steps_le vals i
    simp only [executeGate]
    omega
  | binary ff ft tf tt i j =>
    have hi := readWire_steps_le vals i
    have hj := readWire_steps_le vals j
    simp only [executeGate]
    omega

def execute (inputs : List Bool) : List Bool → List Gate → Execution (List Bool)
  | vals, [] => ⟨vals, 0⟩
  | vals, g :: gs =>
    let e := executeGate inputs vals g
    let stored := appendBit vals e.value
    let rest := execute inputs stored.value gs
    ⟨rest.value, e.steps + stored.steps + rest.steps + 1⟩

theorem execute_value_length (inputs vals : List Bool) (code : List Gate) :
    (execute inputs vals code).value.length = vals.length + code.length := by
  induction code generalizing vals with
  | nil => simp [execute]
  | cons g gs ih =>
    simp only [execute, ih, appendBit_value, List.length_append,
      List.length_cons, List.length_nil]
    omega

theorem execute_lower_value {n : ℕ} (inputs vals : List Bool) (code : List (CGate n)) :
    (execute inputs vals (code.map lowerGate)).value =
      runFrom (fun i => inputs.getD i.val false) vals code := by
  induction code generalizing vals with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, execute, ih, appendBit_value, executeGate_lower_value, runFrom]

/-- Derived from the executed scans and writes, including their growing wire
store. Gate reuse is handled by counting each lookup when it actually occurs. -/
theorem execute_steps_le (inputs vals : List Bool) (code : List Gate) :
    (execute inputs vals code).steps ≤
      7 * code.length * (inputs.length + vals.length + code.length + 1) := by
  induction code generalizing vals with
  | nil => simp [execute]
  | cons g gs ih =>
    have hg := executeGate_steps_le inputs vals g
    have hr := ih (appendBit vals (executeGate inputs vals g).value).value
    simp only [appendBit_value, List.length_append, List.length_singleton] at hr
    simp only [execute, appendBit_steps, appendBit_value, List.length_cons]
    nlinarith

theorem execute_lower_steps_le {n : ℕ} (inputs vals : List Bool) (code : List (CGate n)) :
    (execute inputs vals (code.map lowerGate)).steps ≤
      7 * code.length * (inputs.length + vals.length + code.length + 1) := by
  simpa only [List.length_map] using execute_steps_le inputs vals (code.map lowerGate)

/-- Substituting a proved gate budget controls this evaluator's concrete
traversal counter. Translation and circuit generation are outside this call. -/
theorem execute_lower_steps_le_of_gate_bound {n : ℕ} (inputs vals : List Bool)
    (code : List (CGate n)) (B : ℕ) (h : code.length ≤ B) :
    (execute inputs vals (code.map lowerGate)).steps ≤
      7 * B * (inputs.length + vals.length + B + 1) := by
  exact (execute_lower_steps_le inputs vals code).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 7 h) (by omega))

/-- Output materialization performs and counts every requested wire read. -/
def collectWord (vals : List Bool) : List ℕ → Execution (List Bool)
  | [] => ⟨[], 0⟩
  | i :: is =>
    let b := readWire vals i
    let rest := collectWord vals is
    ⟨b.value :: rest.value, b.steps + rest.steps + 1⟩

theorem collectWord_value (vals : List Bool) (word : List ℕ) :
    (collectWord vals word).value = word.map (fun i => vals.getD i false) := by
  induction word with
  | nil => rfl
  | cons i is ih => simp only [collectWord, List.map_cons, readWire_value, ih]

theorem collectWord_steps_le (vals : List Bool) (word : List ℕ) :
    (collectWord vals word).steps ≤ word.length * (vals.length + 2) := by
  induction word with
  | nil => simp [collectWord]
  | cons i is ih =>
    have h := readWire_steps_le vals i
    simp only [collectWord, List.length_cons]
    nlinarith

/-- Evaluate a stored program and materialize two output words from its wire
store, retaining a counter for both phases. -/
def executePair (inputs vals : List Bool) (code : List Gate) (xs ys : List ℕ) :
    Execution (List Bool × List Bool) :=
  let e := execute inputs vals code
  let x := collectWord e.value xs
  let y := collectWord e.value ys
  ⟨(x.value, y.value), e.steps + x.steps + y.steps + 1⟩

theorem executePair_value (inputs vals : List Bool) (code : List Gate) (xs ys : List ℕ) :
    (executePair inputs vals code xs ys).value =
      (xs.map (fun i => (execute inputs vals code).value.getD i false),
        ys.map (fun i => (execute inputs vals code).value.getD i false)) := by
  simp only [executePair, collectWord_value]

theorem executePair_steps_le (inputs vals : List Bool) (code : List Gate) (xs ys : List ℕ) :
    (executePair inputs vals code xs ys).steps ≤
      7 * code.length * (inputs.length + vals.length + code.length + 1) +
        (xs.length + ys.length) * (vals.length + code.length + 2) + 1 := by
  have he := execute_steps_le inputs vals code
  have hx := collectWord_steps_le (execute inputs vals code).value xs
  have hy := collectWord_steps_le (execute inputs vals code).value ys
  rw [execute_value_length] at hx hy
  simp only [executePair]
  nlinarith

theorem executePair_lower_steps_le {n : ℕ} (inputs vals : List Bool)
    (code : List (CGate n)) (xs ys : List ℕ) (B R : ℕ)
    (hc : code.length ≤ B) (hr : xs.length + ys.length ≤ R) :
    (executePair inputs vals (code.map lowerGate) xs ys).steps ≤
      7 * B * (inputs.length + vals.length + B + 1) +
        R * (vals.length + B + 2) + 1 := by
  have h := executePair_steps_le inputs vals (code.map lowerGate) xs ys
  simp only [List.length_map] at h
  apply h.trans
  exact Nat.add_le_add_right (Nat.add_le_add
    (Nat.mul_le_mul (Nat.mul_le_mul_left 7 hc) (by omega))
    (Nat.mul_le_mul hr (by omega))) 1

end GodMoveBooleanExecutionCost

#print axioms GodMoveBooleanExecutionCost.readWire_value
#print axioms GodMoveBooleanExecutionCost.readWire_steps_le
#print axioms GodMoveBooleanExecutionCost.appendBit_value
#print axioms GodMoveBooleanExecutionCost.appendBit_steps
#print axioms GodMoveBooleanExecutionCost.executeGate_lower_value
#print axioms GodMoveBooleanExecutionCost.execute_value_length
#print axioms GodMoveBooleanExecutionCost.execute_lower_value
#print axioms GodMoveBooleanExecutionCost.execute_steps_le
#print axioms GodMoveBooleanExecutionCost.execute_lower_steps_le_of_gate_bound
#print axioms GodMoveBooleanExecutionCost.collectWord_value
#print axioms GodMoveBooleanExecutionCost.collectWord_steps_le
#print axioms GodMoveBooleanExecutionCost.executePair_value
#print axioms GodMoveBooleanExecutionCost.executePair_steps_le
#print axioms GodMoveBooleanExecutionCost.executePair_lower_steps_le
