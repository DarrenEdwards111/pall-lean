import GodMoveBinaryRationalBackend

/-!
# Counted packing and reference layouts for the binary rational backend

The programs below recurse over the lists and natural-number indices they
actually consume. Their counters include copying the left side of append,
padding, trimming, reference generation and width/layout arithmetic. Natural
zero/successor inspection and construction are primitives of this traversal
model; shared list tails and stored natural values need not be copied deeply.

Erasure matches the existing packing and resizing operations exactly. These
are Boolean/list/index traversal bounds, not native allocation bounds or a
compilation theorem for a uniform tape machine. Circuit generation and
truth-table lowering remain outside the combined scalar counter.
-/

namespace GodMoveBinaryPackingCost

open GodMoveBooleanExecutionCost GodMoveBinaryScalarExecution
open GodMoveRationalWireEncoding GodMoveBinaryRationalBackend

/-- Count both the list visit and the successor of the running length. -/
def lengthFrom {α : Type*} (acc : ℕ) : List α → Execution ℕ
  | [] => ⟨acc, 1⟩
  | _ :: xs =>
    let rest := lengthFrom (acc + 1) xs
    ⟨rest.value, rest.steps + 2⟩

theorem lengthFrom_value {α : Type*} (acc : ℕ) (xs : List α) :
    (lengthFrom acc xs).value = acc + xs.length := by
  induction xs generalizing acc with
  | nil => simp [lengthFrom]
  | cons x xs ih => simp only [lengthFrom, ih, List.length_cons]; omega

theorem lengthFrom_steps {α : Type*} (acc : ℕ) (xs : List α) :
    (lengthFrom acc xs).steps = 2 * xs.length + 1 := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp only [lengthFrom, ih, List.length_cons]; omega

def appendList {α : Type*} : List α → List α → Execution (List α)
  | [], ys => ⟨ys, 1⟩
  | x :: xs, ys =>
    let rest := appendList xs ys
    ⟨x :: rest.value, rest.steps + 1⟩

theorem appendList_value {α : Type*} (xs ys : List α) :
    (appendList xs ys).value = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [appendList, ih]

theorem appendList_steps {α : Type*} (xs ys : List α) :
    (appendList xs ys).steps = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [appendList, ih]

def replicateList {α : Type*} : ℕ → α → Execution (List α)
  | 0, _ => ⟨[], 1⟩
  | k + 1, x =>
    let rest := replicateList k x
    ⟨x :: rest.value, rest.steps + 1⟩

theorem replicateList_value {α : Type*} (k : ℕ) (x : α) :
    (replicateList k x).value = List.replicate k x := by
  induction k with
  | zero => rfl
  | succ k ih => simp [replicateList, ih, List.replicate_succ]

theorem replicateList_steps {α : Type*} (k : ℕ) (x : α) :
    (replicateList k x).steps = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [replicateList, ih]

def takeList {α : Type*} : ℕ → List α → Execution (List α)
  | 0, _ => ⟨[], 1⟩
  | _ + 1, [] => ⟨[], 1⟩
  | k + 1, x :: xs =>
    let rest := takeList k xs
    ⟨x :: rest.value, rest.steps + 1⟩

theorem takeList_value {α : Type*} (k : ℕ) (xs : List α) :
    (takeList k xs).value = xs.take k := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih => cases xs <;> simp [takeList, ih]

theorem takeList_steps {α : Type*} (k : ℕ) (xs : List α) :
    (takeList k xs).steps = min k xs.length + 1 := by
  induction k generalizing xs with
  | zero => simp [takeList]
  | succ k ih => cases xs <;> simp [takeList, ih, Nat.add_min_add_right]

/-- Layout offsets are constructed through actual successor iterations. -/
def addIndex (a : ℕ) : ℕ → Execution ℕ
  | 0 => ⟨a, 1⟩
  | b + 1 =>
    let rest := addIndex a b
    ⟨rest.value + 1, rest.steps + 1⟩

theorem addIndex_value (a b : ℕ) : (addIndex a b).value = a + b := by
  induction b with
  | zero => rfl
  | succ b ih => simp [addIndex, ih, Nat.add_assoc]

theorem addIndex_steps (a b : ℕ) : (addIndex a b).steps = b + 1 := by
  induction b with
  | zero => rfl
  | succ b ih => simp [addIndex, ih]

def subIndex : ℕ → ℕ → Execution ℕ
  | 0, _ => ⟨0, 1⟩
  | a + 1, 0 => ⟨a + 1, 1⟩
  | a + 1, b + 1 =>
    let rest := subIndex a b
    ⟨rest.value, rest.steps + 1⟩

theorem subIndex_value (a b : ℕ) : (subIndex a b).value = a - b := by
  induction a generalizing b with
  | zero => simp [subIndex]
  | succ a ih => cases b <;> simp [subIndex, ih]

theorem subIndex_steps (a b : ℕ) : (subIndex a b).steps = min a b + 1 := by
  induction a generalizing b with
  | zero => simp [subIndex]
  | succ a ih => cases b <;> simp [subIndex, ih, Nat.add_min_add_right]

/-- Each output reference requires a list cell and the next index successor. -/
def rangeRefs (start : ℕ) : ℕ → Execution (List ℕ)
  | 0 => ⟨[], 1⟩
  | w + 1 =>
    let rest := rangeRefs (start + 1) w
    ⟨start :: rest.value, rest.steps + 2⟩

theorem rangeRefs_value (start w : ℕ) :
    (rangeRefs start w).value = List.range' start w := by
  induction w generalizing start with
  | zero => rfl
  | succ w ih => simp [rangeRefs, ih, List.range'_succ]

theorem rangeRefs_steps (start w : ℕ) : (rangeRefs start w).steps = 2 * w + 1 := by
  induction w generalizing start with
  | zero => rfl
  | succ w ih => simp only [rangeRefs, ih]; omega

def padBitsCounted (w : ℕ) (xs : List Bool) : Execution (List Bool) :=
  let len := lengthFrom 0 xs
  let deficit := subIndex w len.value
  let padding := replicateList deficit.value false
  let result := appendList xs padding.value
  ⟨result.value, len.steps + deficit.steps + padding.steps + result.steps + 1⟩

theorem padBitsCounted_value (w : ℕ) (xs : List Bool) :
    (padBitsCounted w xs).value = padBits w xs := by
  simp only [padBitsCounted, lengthFrom_value, Nat.zero_add, subIndex_value,
    replicateList_value, appendList_value, padBits]

theorem padBitsCounted_steps (w : ℕ) (xs : List Bool) :
    (padBitsCounted w xs).steps = 3 * xs.length + w + 5 := by
  simp only [padBitsCounted, lengthFrom_value, Nat.zero_add, lengthFrom_steps,
    subIndex_value, subIndex_steps, replicateList_steps, appendList_steps]
  omega

theorem padBitsCounted_steps_le (w : ℕ) (xs : List Bool) (h : xs.length ≤ w) :
    (padBitsCounted w xs).steps ≤ 4 * w + 5 := by
  rw [padBitsCounted_steps]
  omega

def packCounted (w : ℕ) (r : FractionBits) : Execution (List Bool) :=
  let num := padBitsCounted w r.numerator
  let den := padBitsCounted w r.denominator
  let firstPart := appendList [r.negative] num.value
  let result := appendList firstPart.value den.value
  ⟨result.value, num.steps + den.steps + firstPart.steps + result.steps + 1⟩

theorem packCounted_value (w : ℕ) (r : FractionBits) :
    (packCounted w r).value = pack w r := by
  simp only [packCounted, padBitsCounted_value, appendList_value, pack]

theorem packCounted_steps_le (w : ℕ) (r : FractionBits)
    (hn : r.numerator.length ≤ w) (hd : r.denominator.length ≤ w) :
    (packCounted w r).steps ≤ 9 * w + 15 := by
  have hn' := padBitsCounted_steps_le w r.numerator hn
  have hd' := padBitsCounted_steps_le w r.denominator hd
  simp only [packCounted, appendList_steps, appendList_value, List.length_append,
    List.length_singleton, padBitsCounted_value, padBits_length w _ hn]
  omega

def packedRefsCounted (start w : ℕ) : Execution FractionRefs :=
  let offset := addIndex (start + 1) w
  let num := rangeRefs (start + 1) w
  let den := rangeRefs offset.value w
  ⟨⟨start, num.value, den.value⟩, offset.steps + num.steps + den.steps + 2⟩

theorem packedRefsCounted_value (start w : ℕ) :
    (packedRefsCounted start w).value = packedRefs start w := by
  simp only [packedRefsCounted, addIndex_value, rangeRefs_value, packedRefs]

theorem packedRefsCounted_steps (start w : ℕ) :
    (packedRefsCounted start w).steps = 5 * w + 5 := by
  simp only [packedRefsCounted, addIndex_steps, rangeRefs_steps]
  omega

/-- One cached padding list is shared by the two append/trim operations. -/
def resizeCounted (r : FractionRefs) (w zeroRef : ℕ) : Execution FractionRefs :=
  let padding := replicateList w zeroRef
  let numPad := appendList r.numerator padding.value
  let denPad := appendList r.denominator padding.value
  let num := takeList w numPad.value
  let den := takeList w denPad.value
  ⟨⟨r.sign, num.value, den.value⟩,
    padding.steps + numPad.steps + denPad.steps + num.steps + den.steps + 1⟩

theorem resizeCounted_value (r : FractionRefs) (w zeroRef : ℕ) :
    (resizeCounted r w zeroRef).value = resize r w zeroRef := by
  simp only [resizeCounted, replicateList_value, appendList_value, takeList_value, resize]

theorem resizeCounted_steps (r : FractionRefs) (w zeroRef : ℕ) :
    (resizeCounted r w zeroRef).steps =
      r.numerator.length + r.denominator.length + 3 * w + 6 := by
  simp only [resizeCounted, replicateList_steps, appendList_steps, takeList_steps,
    appendList_value, List.length_append, replicateList_value, List.length_replicate,
    Nat.min_eq_left (Nat.le_add_left w r.numerator.length),
    Nat.min_eq_left (Nat.le_add_left w r.denominator.length)]
  omega

theorem resizeCounted_represents (vals : List Bool) (r : FractionRefs) (q : ℚ)
    (w zeroRef : ℕ) (hr : Represents vals r q) (hz : vals.getD zeroRef false = false)
    (hf : Fits q w) : Represents vals (resizeCounted r w zeroRef).value q := by
  rw [resizeCounted_value]
  exact resize_represents vals r q w zeroRef hr hz hf

/-- Compute the actual backend width by four traversals with one shared
successor accumulator, rather than uncharged calls to `List.length`. -/
def inputWidthCounted (x y : FractionBits) : Execution ℕ :=
  let a := lengthFrom 1 x.numerator
  let b := lengthFrom a.value x.denominator
  let c := lengthFrom b.value y.numerator
  let d := lengthFrom c.value y.denominator
  ⟨d.value, a.steps + b.steps + c.steps + d.steps + 1⟩

theorem inputWidthCounted_value (x y : FractionBits) :
    (inputWidthCounted x y).value = inputWidth x y := by
  simp only [inputWidthCounted, lengthFrom_value, inputWidth]
  omega

theorem inputWidthCounted_steps (x y : FractionBits) :
    (inputWidthCounted x y).steps = 2 * inputWidth x y + 3 := by
  simp only [inputWidthCounted, lengthFrom_steps, inputWidth]
  omega

structure Prepared where
  width : ℕ
  store : List Bool
  left : FractionRefs
  right : FractionRefs
  start : ℕ
  deriving Repr, DecidableEq

def originalPrepared (x y : FractionBits) : Prepared :=
  ⟨inputWidth x y, inputStore x y, refsX x y, refsY x y, (inputStore x y).length⟩

/-- The prepared store, both reference layouts and the new gate offset are
all obtained from counted programs. No rational denotation is inspected. -/
def prepareInputs (x y : FractionBits) : Execution Prepared :=
  let width := inputWidthCounted x y
  let px := packCounted width.value x
  let py := packCounted width.value y
  let store := appendList px.value py.value
  let left := packedRefsCounted 0 width.value
  let twice := addIndex width.value width.value
  let right := packedRefsCounted (twice.value + 1) width.value
  let size := lengthFrom 0 store.value
  ⟨⟨width.value, store.value, left.value, right.value, size.value⟩,
    width.steps + px.steps + py.steps + store.steps + left.steps + twice.steps +
      right.steps + size.steps + 2⟩

theorem prepareInputs_value (x y : FractionBits) :
    (prepareInputs x y).value = originalPrepared x y := by
  simp only [prepareInputs, inputWidthCounted_value, packCounted_value,
    appendList_value, packedRefsCounted_value, addIndex_value, lengthFrom_value,
    Nat.zero_add, originalPrepared, inputStore, refsX, refsY, two_mul]

theorem prepareInputs_steps_le (x y : FractionBits) :
    (prepareInputs x y).steps ≤ 64 * (inputWidth x y + 1) := by
  have hb := inputWidth_bounds x y
  have hx := packCounted_steps_le (inputWidth x y) x hb.1 hb.2.1
  have hy := packCounted_steps_le (inputWidth x y) y hb.2.2.1 hb.2.2.2
  have hlx := pack_length (inputWidth x y) x hb.1 hb.2.1
  have hly := pack_length (inputWidth x y) y hb.2.2.1 hb.2.2.2
  simp only [prepareInputs, inputWidthCounted_steps, inputWidthCounted_value,
    appendList_steps, packCounted_value, packedRefsCounted_steps, addIndex_steps,
    lengthFrom_steps, appendList_value, List.length_append, hlx, hly]
  omega

theorem prepareInputs_represents (x y : FractionBits) (q r : ℚ)
    (hx : x.Represents q) (hy : y.Represents r) :
    Represents (prepareInputs x y).value.store (prepareInputs x y).value.left q ∧
      Represents (prepareInputs x y).value.store (prepareInputs x y).value.right r := by
  rw [prepareInputs_value]
  exact inputStore_represents x y q r hx hy

/-- Add the executed packing/layout cost to the actual scalar evaluation.
Circuit generation and truth-table lowering are still separate operations. -/
def evaluateWithPacking (op : Op) (x y : FractionBits) : Execution FractionBits :=
  let prep := prepareInputs x y
  let code := compile (n := 0) op prep.value.start prep.value.left prep.value.right
  let result := executeFraction [] prep.value.store code.1 code.2
  ⟨result.value, prep.steps + result.steps + 1⟩

theorem evaluateWithPacking_value (op : Op) (x y : FractionBits) :
    (evaluateWithPacking op x y).value = (evaluate op x y).value := by
  simp only [evaluateWithPacking, prepareInputs_value, originalPrepared, evaluate]

theorem evaluateWithPacking_steps (op : Op) (x y : FractionBits) :
    (evaluateWithPacking op x y).steps =
      (prepareInputs x y).steps + (evaluate op x y).steps + 1 := by
  simp only [evaluateWithPacking, prepareInputs_value, originalPrepared, evaluate]

theorem evaluateWithPacking_steps_le (op : Op) (x y : FractionBits) :
    (evaluateWithPacking op x y).steps ≤ 40000100 * (inputWidth x y + 1) ^ 6 := by
  have hp := prepareInputs_steps_le x y
  have he := (evaluate_steps_le op x y).trans (traversalSteps_le_sixth_power _)
  have hw : inputWidth x y + 1 ≤ (inputWidth x y + 1) ^ 6 := by
    calc
      _ = (inputWidth x y + 1) ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  rw [evaluateWithPacking_steps]
  omega

theorem evaluateWithPacking_correct_and_cost (op : Op) (x y : FractionBits) (q r : ℚ)
    (hx : x.Represents q) (hy : y.Represents r) :
    (evaluateWithPacking op x y).value.Represents (op.value q r) ∧
      (evaluateWithPacking op x y).steps ≤ 40000100 * (inputWidth x y + 1) ^ 6 := by
  constructor
  · rw [evaluateWithPacking_value]
    exact evaluate_represents op x y q r hx hy
  · exact evaluateWithPacking_steps_le op x y

/-- Kernel checks include padding, the nontruncating small-width case,
absolute reference offsets, and truncation/padding of different word lengths. -/
example : padBitsCounted 4 [true] = ⟨[true, false, false, false], 12⟩ := by decide
example : padBitsCounted 2 [true, false, true] = ⟨[true, false, true], 16⟩ := by decide
example : packedRefsCounted 7 2 = ⟨⟨7, [8, 9], [10, 11]⟩, 15⟩ := by decide
example : resizeCounted ⟨7, [8, 9, 10], [11]⟩ 2 0 =
    ⟨⟨7, [8, 9], [11, 0]⟩, 16⟩ := by decide

end GodMoveBinaryPackingCost

#print axioms GodMoveBinaryPackingCost.lengthFrom_value
#print axioms GodMoveBinaryPackingCost.lengthFrom_steps
#print axioms GodMoveBinaryPackingCost.appendList_value
#print axioms GodMoveBinaryPackingCost.appendList_steps
#print axioms GodMoveBinaryPackingCost.takeList_value
#print axioms GodMoveBinaryPackingCost.takeList_steps
#print axioms GodMoveBinaryPackingCost.addIndex_value
#print axioms GodMoveBinaryPackingCost.subIndex_value
#print axioms GodMoveBinaryPackingCost.rangeRefs_value
#print axioms GodMoveBinaryPackingCost.rangeRefs_steps
#print axioms GodMoveBinaryPackingCost.padBitsCounted_value
#print axioms GodMoveBinaryPackingCost.padBitsCounted_steps
#print axioms GodMoveBinaryPackingCost.packCounted_value
#print axioms GodMoveBinaryPackingCost.packCounted_steps_le
#print axioms GodMoveBinaryPackingCost.packedRefsCounted_value
#print axioms GodMoveBinaryPackingCost.packedRefsCounted_steps
#print axioms GodMoveBinaryPackingCost.resizeCounted_value
#print axioms GodMoveBinaryPackingCost.resizeCounted_steps
#print axioms GodMoveBinaryPackingCost.resizeCounted_represents
#print axioms GodMoveBinaryPackingCost.inputWidthCounted_value
#print axioms GodMoveBinaryPackingCost.inputWidthCounted_steps
#print axioms GodMoveBinaryPackingCost.prepareInputs_value
#print axioms GodMoveBinaryPackingCost.prepareInputs_steps_le
#print axioms GodMoveBinaryPackingCost.evaluateWithPacking_value
#print axioms GodMoveBinaryPackingCost.evaluateWithPacking_steps
#print axioms GodMoveBinaryPackingCost.evaluateWithPacking_correct_and_cost
