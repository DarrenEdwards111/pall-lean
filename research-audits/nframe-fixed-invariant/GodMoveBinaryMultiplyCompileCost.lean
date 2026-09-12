import GodMoveBinaryPackingCost

/-!
# Counted generation of the binary adder and variable multiplier

These executable compilers build their gate lists recursively. The returned
programs erase exactly to the existing adder and multiplier, and their counters
include the executed list copies, lengths, padding, zips, output references,
and successor-based index arithmetic. Fixed gate/list constructors are charged
explicitly. No counter is obtained by assigning a gate bound to the old compiler.

The model shares stored natural indices and immutable list tails, as in
`GodMoveBinaryPackingCost`. The bounds concern these traversal primitives;
they are not native-allocation or uniform tape-machine compilation bounds.
-/

namespace GodMoveBinaryMultiplyCompileCost

open GodMoveBooleanExecutionCost GodMoveBinaryPackingCost
open GodMoveBinaryAdder GodMoveBinaryMultiply GodMoveWireSum
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- Five binary-gate constructors, five list cells and the empty terminator
cost eleven fixed construction steps; the two variable offsets are counted. -/
def fullAdderCounted {n : ℕ} (start x y carry : ℕ) : Execution (List (CGate n)) :=
  let i1 := addIndex start 1
  let i3 := addIndex start 3
  ⟨[.bin Bool.xor x y, .bin Bool.and x y, .bin Bool.xor start carry,
      .bin Bool.and start carry, .bin Bool.or i1.value i3.value],
    i1.steps + i3.steps + 11⟩

theorem fullAdderCounted_value {n : ℕ} (start x y carry : ℕ) :
    (fullAdderCounted (n := n) start x y carry).value = fullAdder start x y carry := by
  simp only [fullAdderCounted, addIndex_value, fullAdder]

theorem fullAdderCounted_steps {n : ℕ} (start x y carry : ℕ) :
    (fullAdderCounted (n := n) start x y carry).steps = 17 := rfl

def addBitsCounted {n : ℕ} (start : ℕ) :
    List (ℕ × ℕ) → ℕ → Execution (List (CGate n) × List ℕ)
  | [], carry => ⟨([], [carry]), 2⟩
  | (x, y) :: ps, carry =>
    let nextStart := addIndex start 5
    let nextCarry := addIndex start 4
    let sumRef := addIndex start 2
    let head := fullAdderCounted start x y carry
    let rest := addBitsCounted nextStart.value ps nextCarry.value
    let code := appendList head.value rest.value.1
    ⟨(code.value, sumRef.value :: rest.value.2),
      nextStart.steps + nextCarry.steps + sumRef.steps + head.steps + rest.steps + code.steps + 2⟩

theorem addBitsCounted_value {n : ℕ} (start : ℕ) (ps : List (ℕ × ℕ)) (carry : ℕ) :
    (addBitsCounted (n := n) start ps carry).value = addBits start ps carry := by
  induction ps generalizing start carry with
  | nil => rfl
  | cons p ps ih =>
    cases p
    simp only [addBitsCounted, addIndex_value, fullAdderCounted_value,
      appendList_value, ih, addBits]

theorem addBitsCounted_steps {n : ℕ} (start : ℕ) (ps : List (ℕ × ℕ)) (carry : ℕ) :
    (addBitsCounted (n := n) start ps carry).steps = 39 * ps.length + 2 := by
  induction ps generalizing start carry with
  | nil => rfl
  | cons p ps ih =>
    cases p
    simp only [addBitsCounted, addIndex_steps, fullAdderCounted_steps,
      appendList_steps, fullAdderCounted_value, fullAdder_length, ih, List.length_cons]
    omega

/-- Explicit mapping by an AND gate, charging each gate and output list cell. -/
def maskGatesCounted {n : ℕ} (selector : ℕ) : List ℕ → Execution (List (CGate n))
  | [] => ⟨[], 1⟩
  | i :: is =>
    let rest := maskGatesCounted selector is
    ⟨.bin Bool.and selector i :: rest.value, rest.steps + 2⟩

theorem maskGatesCounted_value {n : ℕ} (selector : ℕ) (word : List ℕ) :
    (maskGatesCounted (n := n) selector word).value = word.map (fun i => .bin Bool.and selector i) := by
  induction word with
  | nil => rfl
  | cons i is ih => simp only [maskGatesCounted, List.map_cons, ih]

theorem maskGatesCounted_steps {n : ℕ} (selector : ℕ) (word : List ℕ) :
    (maskGatesCounted (n := n) selector word).steps = 2 * word.length + 1 := by
  induction word with
  | nil => rfl
  | cons i is ih => simp only [maskGatesCounted, ih, List.length_cons]; omega

def maskWordCounted {n : ℕ} (start selector : ℕ) (word : List ℕ) :
    Execution (List (CGate n) × List ℕ) :=
  let len := lengthFrom 0 word
  let gates := maskGatesCounted selector word
  let refs := rangeRefs start len.value
  ⟨(gates.value, refs.value), len.steps + gates.steps + refs.steps + 1⟩

theorem maskWordCounted_value {n : ℕ} (start selector : ℕ) (word : List ℕ) :
    (maskWordCounted (n := n) start selector word).value = maskWord start selector word := by
  simp only [maskWordCounted, lengthFrom_value, Nat.zero_add,
    maskGatesCounted_value, rangeRefs_value, maskWord]

theorem maskWordCounted_steps {n : ℕ} (start selector : ℕ) (word : List ℕ) :
    (maskWordCounted (n := n) start selector word).steps = 6 * word.length + 4 := by
  simp only [maskWordCounted, lengthFrom_value, Nat.zero_add,
    lengthFrom_steps, maskGatesCounted_steps, rangeRefs_steps]
  omega

def zipCounted {α β : Type*} : List α → List β → Execution (List (α × β))
  | [], _ => ⟨[], 1⟩
  | _ :: _, [] => ⟨[], 1⟩
  | x :: xs, y :: ys =>
    let rest := zipCounted xs ys
    ⟨(x, y) :: rest.value, rest.steps + 2⟩

theorem zipCounted_value {α β : Type*} (xs : List α) (ys : List β) :
    (zipCounted xs ys).value = xs.zip ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => cases ys <;> simp only [zipCounted, List.zip_cons_cons, List.zip_nil_right, ih]

theorem zipCounted_steps {α β : Type*} (xs : List α) (ys : List β) :
    (zipCounted xs ys).steps = 2 * min xs.length ys.length + 1 := by
  induction xs generalizing ys with
  | nil => simp [zipCounted]
  | cons x xs ih => cases ys <;> simp [zipCounted, ih, Nat.add_min_add_right, Nat.mul_add]

def paddedPairsCounted (zeroRef : ℕ) (xs ys : List ℕ) : Execution (List (ℕ × ℕ)) :=
  let lx := lengthFrom 0 xs
  let ly := lengthFrom 0 ys
  let px := replicateList ly.value zeroRef
  let py := replicateList lx.value zeroRef
  let xx := appendList xs px.value
  let yy := appendList ys py.value
  let pairs := zipCounted xx.value yy.value
  ⟨pairs.value, lx.steps + ly.steps + px.steps + py.steps + xx.steps + yy.steps + pairs.steps + 1⟩

theorem paddedPairsCounted_value (zeroRef : ℕ) (xs ys : List ℕ) :
    (paddedPairsCounted zeroRef xs ys).value = paddedPairs zeroRef xs ys := by
  simp only [paddedPairsCounted, lengthFrom_value, Nat.zero_add, replicateList_value,
    appendList_value, zipCounted_value, paddedPairs]

theorem paddedPairsCounted_steps (zeroRef : ℕ) (xs ys : List ℕ) :
    (paddedPairsCounted zeroRef xs ys).steps = 6 * (xs.length + ys.length) + 8 := by
  simp only [paddedPairsCounted, lengthFrom_value, Nat.zero_add, lengthFrom_steps,
    replicateList_steps, appendList_steps, zipCounted_steps, appendList_value,
    List.length_append, replicateList_value, List.length_replicate]
  omega

def multiplyBitsCounted {n : ℕ} (start zeroRef : ℕ) :
    List ℕ → List ℕ → Execution (List (CGate n) × List ℕ)
  | [], _ => ⟨([], []), 2⟩
  | x :: xs, ys =>
    let rest := multiplyBitsCounted start zeroRef xs ys
    let restLen := lengthFrom 0 rest.value.1
    let maskStart := addIndex start restLen.value
    let masked := maskWordCounted maskStart.value x ys
    let maskLen := lengthFrom 0 masked.value.1
    let sumStart := addIndex maskStart.value maskLen.value
    let pairs := paddedPairsCounted zeroRef (zeroRef :: rest.value.2) masked.value.2
    let addition := addBitsCounted sumStart.value pairs.value zeroRef
    let firstPart := appendList rest.value.1 masked.value.1
    let code := appendList firstPart.value addition.value.1
    ⟨(code.value, addition.value.2),
      rest.steps + restLen.steps + maskStart.steps + masked.steps + maskLen.steps +
        sumStart.steps + pairs.steps + addition.steps + firstPart.steps + code.steps + 2⟩

theorem multiplyBitsCounted_value {n : ℕ} (start zeroRef : ℕ) (xs ys : List ℕ) :
    (multiplyBitsCounted (n := n) start zeroRef xs ys).value = multiplyBits start zeroRef xs ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [multiplyBitsCounted, ih, lengthFrom_value, Nat.zero_add, addIndex_value,
      maskWordCounted_value, paddedPairsCounted_value, addBitsCounted_value,
      appendList_value, multiplyBits]

/-- The recurrence includes both copies of the accumulated gate prefix. -/
theorem multiplyBitsCounted_steps_cons {n : ℕ} (start zeroRef x : ℕ) (xs ys : List ℕ) :
    (multiplyBitsCounted (n := n) start zeroRef (x :: xs) ys).steps =
      (multiplyBitsCounted (n := n) start zeroRef xs ys).steps +
        5 * (multiplyBits (n := n) start zeroRef xs ys).1.length +
        10 * ys.length + 45 * (xs.length * (ys.length + 2) + 1 + ys.length) + 22 := by
  simp only [multiplyBitsCounted, lengthFrom_steps, lengthFrom_value, Nat.zero_add,
    addIndex_steps, maskWordCounted_steps, maskWordCounted_value,
    paddedPairsCounted_steps, paddedPairsCounted_value, addBitsCounted_steps,
    appendList_steps, appendList_value, List.length_append, List.length_cons,
    multiplyBitsCounted_value, maskWord_gate_count, maskWord_word_length,
    multiplyBits_word_length, paddedPairs_length]
  omega

theorem multiplyBitsCounted_steps_le {n : ℕ} (start zeroRef : ℕ) (xs ys : List ℕ) :
    (multiplyBitsCounted (n := n) start zeroRef xs ys).steps ≤
      100 * (xs.length + 1) ^ 3 * (ys.length + 2) := by
  induction xs with
  | nil => simp [multiplyBitsCounted]; omega
  | cons x xs ih =>
    rw [multiplyBitsCounted_steps_cons]
    have hg := multiplyBits_gate_count_le (n := n) start zeroRef xs ys
    simp only [List.length_cons]
    nlinarith [Nat.zero_le (xs.length ^ 2 * ys.length),
      Nat.zero_le (xs.length * ys.length)]

def productBitsCounted {n : ℕ} (start zeroRef : ℕ) (xs ys : List ℕ) :
    Execution (List (CGate n) × List ℕ) :=
  let code := multiplyBitsCounted start zeroRef xs ys
  let lx := lengthFrom 0 xs
  let width := lengthFrom lx.value ys
  let padding := replicateList width.value zeroRef
  let padded := appendList code.value.2 padding.value
  let refs := takeList width.value padded.value
  ⟨(code.value.1, refs.value),
    code.steps + lx.steps + width.steps + padding.steps + padded.steps + refs.steps + 1⟩

theorem productBitsCounted_value {n : ℕ} (start zeroRef : ℕ) (xs ys : List ℕ) :
    (productBitsCounted (n := n) start zeroRef xs ys).value = productBits start zeroRef xs ys := by
  simp only [productBitsCounted, multiplyBitsCounted_value, lengthFrom_value,
    Nat.zero_add, replicateList_value, appendList_value, takeList_value, productBits]

theorem productBitsCounted_steps {n : ℕ} (start zeroRef : ℕ) (xs ys : List ℕ) :
    (productBitsCounted (n := n) start zeroRef xs ys).steps =
      (multiplyBitsCounted (n := n) start zeroRef xs ys).steps +
        xs.length * (ys.length + 2) + 4 * (xs.length + ys.length) + 6 := by
  simp only [productBitsCounted, lengthFrom_steps, lengthFrom_value, Nat.zero_add,
    replicateList_steps, appendList_steps, takeList_steps, appendList_value,
    List.length_append, replicateList_value, List.length_replicate,
    multiplyBitsCounted_value, multiplyBits_word_length]
  omega

theorem productBitsCounted_steps_le {n : ℕ} (start zeroRef : ℕ) (xs ys : List ℕ) :
    (productBitsCounted (n := n) start zeroRef xs ys).steps ≤
      128 * (xs.length + 1) ^ 3 * (ys.length + 2) := by
  rw [productBitsCounted_steps]
  have hm := multiplyBitsCounted_steps_le (n := n) start zeroRef xs ys
  nlinarith [Nat.zero_le (xs.length ^ 2 * ys.length), Nat.zero_le (xs.length * ys.length)]

theorem productBitsCounted_steps_le_total {n : ℕ} (start zeroRef : ℕ) (xs ys : List ℕ) :
    (productBitsCounted (n := n) start zeroRef xs ys).steps ≤
      128 * (start + xs.length + ys.length + 2) ^ 4 := by
  calc
    _ ≤ 128 * (xs.length + 1) ^ 3 * (ys.length + 2) :=
      productBitsCounted_steps_le start zeroRef xs ys
    _ ≤ 128 * (start + xs.length + ys.length + 2) ^ 3 *
        (start + xs.length + ys.length + 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)) (by omega)
    _ = _ := by ring

theorem addBitsCounted_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (pairs : List (ℕ × ℕ)) (carry : ℕ)
    (hp : ∀ p ∈ pairs, p.1 < vals.length ∧ p.2 < vals.length) (hc : carry < vals.length) :
    let result := addBitsCounted (n := n) vals.length pairs carry
    wordValue (runFrom a vals result.value.1) result.value.2 =
      wordValue vals (pairs.map Prod.fst) + wordValue vals (pairs.map Prod.snd) +
        (vals.getD carry false).toNat := by
  dsimp only
  rw [addBitsCounted_value]
  exact addBits_spec a vals pairs carry hp hc

/-- The returned program is the verified multiplier, not just an equal gate count. -/
theorem productBitsCounted_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (zeroRef : ℕ) (xs ys : List ℕ) (hz : zeroRef < vals.length)
    (hzval : vals.getD zeroRef false = false)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length) :
    let result := productBitsCounted (n := n) vals.length zeroRef xs ys
    wordValue (runFrom a vals result.value.1) result.value.2 = wordValue vals xs * wordValue vals ys := by
  dsimp only
  rw [productBitsCounted_value]
  exact productBits_spec a vals zeroRef xs ys hz hzval hx hy

example : (addBitsCounted (n := 0) 5 [(0, 2), (1, 3)] 4).steps = 80 := by decide
example : (maskWordCounted (n := 0) 9 0 [1, 2, 3]).steps = 22 := by decide
example : paddedPairsCounted 1 [2] [3, 4] = ⟨[(2, 3), (1, 4), (1, 1)], 26⟩ := by decide

private def kernelProduct : ℕ × ℕ :=
  let result := productBitsCounted (n := 0) 5 4 [0, 1] [2, 3]
  (wordValue (runFrom (fun i => Fin.elim0 i) [true, true, true, true, false]
    result.value.1) result.value.2, result.steps)

set_option maxRecDepth 4096 in
example : kernelProduct = (9, 651) := by decide

example : (productBitsCounted (n := 0) 5 4 [] [2, 3]).steps = 16 := by decide

end GodMoveBinaryMultiplyCompileCost

#print axioms GodMoveBinaryMultiplyCompileCost.fullAdderCounted_value
#print axioms GodMoveBinaryMultiplyCompileCost.addBitsCounted_value
#print axioms GodMoveBinaryMultiplyCompileCost.addBitsCounted_steps
#print axioms GodMoveBinaryMultiplyCompileCost.maskWordCounted_value
#print axioms GodMoveBinaryMultiplyCompileCost.maskWordCounted_steps
#print axioms GodMoveBinaryMultiplyCompileCost.zipCounted_value
#print axioms GodMoveBinaryMultiplyCompileCost.paddedPairsCounted_value
#print axioms GodMoveBinaryMultiplyCompileCost.paddedPairsCounted_steps
#print axioms GodMoveBinaryMultiplyCompileCost.multiplyBitsCounted_value
#print axioms GodMoveBinaryMultiplyCompileCost.multiplyBitsCounted_steps_cons
#print axioms GodMoveBinaryMultiplyCompileCost.multiplyBitsCounted_steps_le
#print axioms GodMoveBinaryMultiplyCompileCost.productBitsCounted_value
#print axioms GodMoveBinaryMultiplyCompileCost.productBitsCounted_steps
#print axioms GodMoveBinaryMultiplyCompileCost.productBitsCounted_steps_le
#print axioms GodMoveBinaryMultiplyCompileCost.productBitsCounted_steps_le_total
#print axioms GodMoveBinaryMultiplyCompileCost.addBitsCounted_spec
#print axioms GodMoveBinaryMultiplyCompileCost.productBitsCounted_spec
