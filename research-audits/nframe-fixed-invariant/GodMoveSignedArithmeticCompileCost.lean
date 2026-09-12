import GodMoveBinaryDivisionCompileCost
import GodMoveSignedArithmetic

/-!
# Counted generation of signed addition and subtraction

The executable builders below materialize the same gates and output references
as the existing verified signed circuits. Every variable-sized zip, code copy,
length traversal and index offset is performed by a counted primitive. Existing
natural indices and immutable list tails are shared, as in BinaryPackingCost.
Fixed gate/list construction is charged separately. These are generation
counters in that traversal model, not native or tape-machine execution times.
-/

namespace GodMoveSignedArithmeticCompileCost

open GodMoveBooleanExecutionCost GodMoveBinaryPackingCost
open GodMoveBinaryMultiplyCompileCost GodMoveBinaryDivisionCompileCost
open GodMoveBinaryAdder GodMoveBinarySubtract GodMoveBinaryDivision
open GodMoveSignedArithmetic GodMoveRationalWireEncoding
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

def absDifferenceCounted {n : ℕ} (start : ℕ) (xs ys : List ℕ) (z : ℕ) :
    Execution (List (CGate n) × (ℕ × List ℕ)) :=
  let xy := zipCounted xs ys
  let d := subtractBitsCounted start xy.value z
  let dl := lengthFrom 0 d.value.1
  let es := addIndex start dl.value
  let yx := zipCounted ys xs
  let e := subtractBitsCounted es.value yx.value z
  let el := lengthFrom 0 e.value.1
  let ms := addIndex es.value el.value
  let pairs := zipCounted e.value.2.1 d.value.2.1
  let m := muxBitsCounted ms.value d.value.2.2 pairs.value
  let de := appendList d.value.1 e.value.1
  let code := appendList de.value m.value.1
  ⟨(code.value, (d.value.2.2, m.value.2)),
    xy.steps + d.steps + dl.steps + es.steps + yx.steps + e.steps + el.steps +
      ms.steps + pairs.steps + m.steps + de.steps + code.steps + 2⟩

theorem absDifferenceCounted_value {n : ℕ} (start : ℕ) (xs ys : List ℕ) (z : ℕ) :
    (absDifferenceCounted (n := n) start xs ys z).value = absDifference start xs ys z := by
  simp only [absDifferenceCounted, zipCounted_value, subtractBitsCounted_value,
    lengthFrom_value, Nat.zero_add, addIndex_value, muxBitsCounted_value,
    appendList_value, absDifference]

theorem absDifferenceCounted_steps {n : ℕ} (start : ℕ) (xs ys : List ℕ) (z : ℕ)
    (hlen : xs.length = ys.length) :
    (absDifferenceCounted (n := n) start xs ys z).steps = 262 * xs.length + 17 := by
  simp only [absDifferenceCounted, zipCounted_steps, subtractBitsCounted_steps,
    lengthFrom_steps, lengthFrom_value, Nat.zero_add, addIndex_steps,
    muxBitsCounted_steps, appendList_steps, zipCounted_value, subtractBitsCounted_value,
    appendList_value, subtractBits_gate_count, subtractBits_word_length,
    List.length_zip, List.length_append, hlen, min_self]
  omega

/-- Three gates and three cells with a terminator cost seven fixed steps. -/
def signControlCounted {n : ℕ} (start sx sy borrow : ℕ) : Execution (List (CGate n)) :=
  let next := addIndex start 1
  ⟨[.bin Bool.xor sx sy, .bin Bool.and start borrow, .bin Bool.xor sx next.value],
    next.steps + 7⟩

theorem signControlCounted_value {n : ℕ} (start sx sy borrow : ℕ) :
    (signControlCounted (n := n) start sx sy borrow).value = signControl start sx sy borrow := by
  simp only [signControlCounted, addIndex_value, signControl]

theorem signControlCounted_steps {n : ℕ} (start sx sy borrow : ℕ) :
    (signControlCounted (n := n) start sx sy borrow).steps = 9 := rfl

def addSignedCounted {n : ℕ} (start sx : ℕ) (xs : List ℕ) (sy : ℕ) (ys : List ℕ) :
    Execution (List (CGate n) × (ℕ × List ℕ)) :=
  let ss := addIndex start 1
  let pairs := zipCounted xs ys
  let sum := addBitsCounted ss.value pairs.value start
  let sl := lengthFrom 0 sum.value.1
  let ds := addIndex ss.value sl.value
  let diff := absDifferenceCounted ds.value xs ys start
  let dl := lengthFrom 0 diff.value.1
  let cs := addIndex ds.value dl.value
  let ctrl := signControlCounted cs.value sx sy diff.value.2.1
  let cl := lengthFrom 0 ctrl.value
  let ms := addIndex cs.value cl.value
  let padded := appendList diff.value.2.2 [start]
  let mp := zipCounted padded.value sum.value.2
  let mag := muxBitsCounted ms.value cs.value mp.value
  let c0 := appendList [.cst false] sum.value.1
  let c1 := appendList c0.value diff.value.1
  let c2 := appendList c1.value ctrl.value
  let code := appendList c2.value mag.value.1
  let signRef := addIndex cs.value 2
  ⟨(code.value, (signRef.value, mag.value.2)),
    ss.steps + pairs.steps + sum.steps + sl.steps + ds.steps + diff.steps + dl.steps +
      cs.steps + ctrl.steps + cl.steps + ms.steps + padded.steps + mp.steps + mag.steps +
      c0.steps + c1.steps + c2.steps + code.steps + signRef.steps + 6⟩

theorem addSignedCounted_value {n : ℕ} (start sx : ℕ) (xs : List ℕ) (sy : ℕ) (ys : List ℕ) :
    (addSignedCounted (n := n) start sx xs sy ys).value = addSigned start sx xs sy ys := by
  simp only [addSignedCounted, addIndex_value, zipCounted_value, addBitsCounted_value,
    lengthFrom_value, Nat.zero_add, absDifferenceCounted_value, signControlCounted_value,
    appendList_value, muxBitsCounted_value, addSigned]

theorem addSignedCounted_steps {n : ℕ} (start sx : ℕ) (xs : List ℕ)
    (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (addSignedCounted (n := n) start sx xs sy ys).steps = 453 * xs.length + 94 := by
  simp only [addSignedCounted, addIndex_steps, zipCounted_steps, addBitsCounted_steps,
    lengthFrom_steps, lengthFrom_value, Nat.zero_add,
    absDifferenceCounted_steps _ _ _ _ hlen, signControlCounted_steps,
    muxBitsCounted_steps, appendList_steps, addBitsCounted_value,
    absDifferenceCounted_value, signControlCounted_value, zipCounted_value,
    appendList_value, addBits_gate_count, addBits_word_length,
    absDifference_gate_count _ _ _ _ hlen, absDifference_word_length _ _ _ _ hlen,
    signControl_length, List.length_zip, List.length_append, List.length_singleton,
    hlen, min_self]
  omega

theorem addSignedCounted_steps_le {n : ℕ} (start sx : ℕ) (xs : List ℕ)
    (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (addSignedCounted (n := n) start sx xs sy ys).steps ≤ 512 * (xs.length + 1) := by
  rw [addSignedCounted_steps _ _ _ _ _ hlen]
  omega

def subtractSignedCounted {n : ℕ} (start sx : ℕ) (xs : List ℕ) (sy : ℕ) (ys : List ℕ) :
    Execution (List (CGate n) × (ℕ × List ℕ)) :=
  let next := addIndex start 1
  let result := addSignedCounted next.value sx xs start ys
  ⟨(.un Bool.not sy :: result.value.1, result.value.2), next.steps + result.steps + 3⟩

theorem subtractSignedCounted_value {n : ℕ} (start sx : ℕ) (xs : List ℕ)
    (sy : ℕ) (ys : List ℕ) :
    (subtractSignedCounted (n := n) start sx xs sy ys).value = subtractSigned start sx xs sy ys := by
  simp only [subtractSignedCounted, addIndex_value, addSignedCounted_value, subtractSigned]

theorem subtractSignedCounted_steps {n : ℕ} (start sx : ℕ) (xs : List ℕ)
    (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (subtractSignedCounted (n := n) start sx xs sy ys).steps = 453 * xs.length + 99 := by
  simp only [subtractSignedCounted, addIndex_steps, addSignedCounted_steps _ _ _ _ _ hlen]
  omega

theorem subtractSignedCounted_steps_le {n : ℕ} (start sx : ℕ) (xs : List ℕ)
    (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (subtractSignedCounted (n := n) start sx xs sy ys).steps ≤ 512 * (xs.length + 1) := by
  rw [subtractSignedCounted_steps _ _ _ _ _ hlen]
  omega

theorem addSignedCounted_word_length {n : ℕ} (start sx : ℕ) (xs : List ℕ)
    (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (addSignedCounted (n := n) start sx xs sy ys).value.2.2.length = xs.length + 1 := by
  rw [addSignedCounted_value]
  exact addSigned_word_length start sx xs sy ys hlen

theorem subtractSignedCounted_word_length {n : ℕ} (start sx : ℕ) (xs : List ℕ)
    (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (subtractSignedCounted (n := n) start sx xs sy ys).value.2.2.length = xs.length + 1 := by
  rw [subtractSignedCounted_value]
  exact subtractSigned_word_length start sx xs sy ys hlen

theorem addSignedCounted_refs_lt {n : ℕ} (start sx : ℕ) (xs : List ℕ)
    (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (addSignedCounted (n := n) start sx xs sy ys).value.2.1 <
      start + (addSignedCounted (n := n) start sx xs sy ys).value.1.length ∧
    ∀ i ∈ (addSignedCounted (n := n) start sx xs sy ys).value.2.2,
      i < start + (addSignedCounted (n := n) start sx xs sy ys).value.1.length := by
  rw [addSignedCounted_value]
  exact addSigned_refs_lt start sx xs sy ys hlen

theorem subtractSignedCounted_refs_lt {n : ℕ} (start sx : ℕ) (xs : List ℕ)
    (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (subtractSignedCounted (n := n) start sx xs sy ys).value.2.1 <
      start + (subtractSignedCounted (n := n) start sx xs sy ys).value.1.length ∧
    ∀ i ∈ (subtractSignedCounted (n := n) start sx xs sy ys).value.2.2,
      i < start + (subtractSignedCounted (n := n) start sx xs sy ys).value.1.length := by
  rw [subtractSignedCounted_value]
  exact subtractSigned_refs_lt start sx xs sy ys hlen

theorem addSignedCounted_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (sx : ℕ) (xs : List ℕ) (sy : ℕ) (ys : List ℕ)
    (hlen : xs.length = ys.length) (hsx : sx < vals.length) (hsy : sy < vals.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length) :
    let result := addSignedCounted (n := n) vals.length sx xs sy ys
    signedValue (runFrom a vals result.value.1) result.value.2.1 result.value.2.2 =
      signedValue vals sx xs + signedValue vals sy ys := by
  dsimp only
  rw [addSignedCounted_value]
  exact addSigned_spec a vals sx xs sy ys hlen hsx hsy hx hy

theorem subtractSignedCounted_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (sx : ℕ) (xs : List ℕ) (sy : ℕ) (ys : List ℕ)
    (hlen : xs.length = ys.length) (hsx : sx < vals.length) (hsy : sy < vals.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length) :
    let result := subtractSignedCounted (n := n) vals.length sx xs sy ys
    signedValue (runFrom a vals result.value.1) result.value.2.1 result.value.2.2 =
      signedValue vals sx xs - signedValue vals sy ys := by
  dsimp only
  rw [subtractSignedCounted_value]
  exact subtractSigned_spec a vals sx xs sy ys hlen hsx hsy hx hy

private def signedTwo : ℤ × ℕ :=
  let result := addSignedCounted (n := 0) 6 0 [1, 2] 3 [4, 5]
  let vals := [true, true, true, false, true, false]
  (signedValue (runFrom (fun i => Fin.elim0 i) vals result.value.1)
    result.value.2.1 result.value.2.2, result.steps)

/- The generated two-bit program computes `-3 + 1` and reports its actual
generation counter. Kernel reduction also checks the empty-magnitude case. -/
set_option maxRecDepth 20000 in
example : signedTwo = (-2, 1000) := by decide

example : (addSignedCounted (n := 0) 2 0 [] 1 []).steps = 94 := by decide
example : (subtractSignedCounted (n := 0) 2 0 [] 1 []).steps = 99 := by decide

end GodMoveSignedArithmeticCompileCost

#print axioms GodMoveSignedArithmeticCompileCost.absDifferenceCounted_value
#print axioms GodMoveSignedArithmeticCompileCost.absDifferenceCounted_steps
#print axioms GodMoveSignedArithmeticCompileCost.signControlCounted_value
#print axioms GodMoveSignedArithmeticCompileCost.signControlCounted_steps
#print axioms GodMoveSignedArithmeticCompileCost.addSignedCounted_value
#print axioms GodMoveSignedArithmeticCompileCost.addSignedCounted_steps
#print axioms GodMoveSignedArithmeticCompileCost.addSignedCounted_steps_le
#print axioms GodMoveSignedArithmeticCompileCost.subtractSignedCounted_value
#print axioms GodMoveSignedArithmeticCompileCost.subtractSignedCounted_steps
#print axioms GodMoveSignedArithmeticCompileCost.subtractSignedCounted_steps_le
#print axioms GodMoveSignedArithmeticCompileCost.addSignedCounted_word_length
#print axioms GodMoveSignedArithmeticCompileCost.subtractSignedCounted_word_length
#print axioms GodMoveSignedArithmeticCompileCost.addSignedCounted_refs_lt
#print axioms GodMoveSignedArithmeticCompileCost.subtractSignedCounted_refs_lt
#print axioms GodMoveSignedArithmeticCompileCost.addSignedCounted_spec
#print axioms GodMoveSignedArithmeticCompileCost.subtractSignedCounted_spec
