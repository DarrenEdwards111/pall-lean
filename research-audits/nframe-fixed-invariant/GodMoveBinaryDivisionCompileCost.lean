import GodMoveBinaryMultiplyCompileCost

/-!
# Counted generation of restoring binary division

The executable compiler constructs the subtractor, selectors, restoring stages,
and zero-divisor mask through counted recursive calls. Length scans, reversal,
padding, zips, reference offsets, trimming and code copies are included. Erasure
identifies the whole program and both output words with the verified divider.

The primitives are the list and unary-index traversals of `BinaryPackingCost`;
stored indices and immutable tails are shared. Counter arithmetic, native
allocation and compilation into a uniform tape machine are outside this model.
-/

namespace GodMoveBinaryDivisionCompileCost

open GodMoveBooleanExecutionCost GodMoveBinaryPackingCost
open GodMoveBinaryMultiplyCompileCost GodMoveBinaryAdder GodMoveBinarySubtract
open GodMoveBinaryDivision
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

def fullSubtractCounted {n : ℕ} (start x y borrow : ℕ) : Execution (List (CGate n)) :=
  let i2 := addIndex start 2
  let i1 := addIndex start 1
  let i6 := addIndex start 6
  let add := fullAdderCounted i2.value x start i1.value
  let first := appendList [.un Bool.not y, .un Bool.not borrow] add.value
  let code := appendList first.value [.un Bool.not i6.value]
  ⟨code.value, i2.steps + i1.steps + i6.steps + add.steps + first.steps + code.steps + 8⟩

theorem fullSubtractCounted_value {n : ℕ} (start x y borrow : ℕ) :
    (fullSubtractCounted (n := n) start x y borrow).value = fullSubtract start x y borrow := by
  simp only [fullSubtractCounted, addIndex_value, fullAdderCounted_value,
    appendList_value, fullSubtract]

theorem fullSubtractCounted_steps {n : ℕ} (start x y borrow : ℕ) :
    (fullSubtractCounted (n := n) start x y borrow).steps = 48 := by
  simp only [fullSubtractCounted, addIndex_steps, appendList_steps, appendList_value,
    fullAdderCounted_value, fullAdderCounted_steps, List.length_append,
    List.length_cons, List.length_nil, fullAdder_length]

def subtractBitsCounted {n : ℕ} (start : ℕ) :
    List (ℕ × ℕ) → ℕ → Execution (List (CGate n) × (List ℕ × ℕ))
  | [], borrow => ⟨([], ([], borrow)), 2⟩
  | (x, y) :: pairs, borrow =>
    let nextStart := addIndex start 8
    let nextBorrow := addIndex start 7
    let out := addIndex start 4
    let head := fullSubtractCounted start x y borrow
    let rest := subtractBitsCounted nextStart.value pairs nextBorrow.value
    let code := appendList head.value rest.value.1
    ⟨(code.value, (out.value :: rest.value.2.1, rest.value.2.2)),
      nextStart.steps + nextBorrow.steps + out.steps + head.steps + rest.steps + code.steps + 2⟩

theorem subtractBitsCounted_value {n : ℕ} (start : ℕ) (pairs : List (ℕ × ℕ)) (borrow : ℕ) :
    (subtractBitsCounted (n := n) start pairs borrow).value = subtractBits start pairs borrow := by
  induction pairs generalizing start borrow with
  | nil => rfl
  | cons p ps ih =>
    cases p
    simp only [subtractBitsCounted, addIndex_value, fullSubtractCounted_value,
      appendList_value, ih, subtractBits]

theorem subtractBitsCounted_steps {n : ℕ} (start : ℕ) (pairs : List (ℕ × ℕ)) (borrow : ℕ) :
    (subtractBitsCounted (n := n) start pairs borrow).steps = 81 * pairs.length + 2 := by
  induction pairs generalizing start borrow with
  | nil => rfl
  | cons p ps ih =>
    cases p
    simp only [subtractBitsCounted, addIndex_steps, fullSubtractCounted_steps,
      appendList_steps, fullSubtractCounted_value, fullSubtract_length, ih, List.length_cons]
    omega

def muxBitCounted {n : ℕ} (start sel x y : ℕ) : Execution (List (CGate n)) :=
  let i1 := addIndex start 1
  ⟨[.bin Bool.and sel x, .bin (fun b v => !b && v) sel y, .bin Bool.or start i1.value],
    i1.steps + 7⟩

theorem muxBitCounted_value {n : ℕ} (start sel x y : ℕ) :
    (muxBitCounted (n := n) start sel x y).value = muxBit start sel x y := by
  simp only [muxBitCounted, addIndex_value, muxBit]

theorem muxBitCounted_steps {n : ℕ} (start sel x y : ℕ) :
    (muxBitCounted (n := n) start sel x y).steps = 9 := rfl

def muxBitsCounted {n : ℕ} (start sel : ℕ) :
    List (ℕ × ℕ) → Execution (List (CGate n) × List ℕ)
  | [] => ⟨([], []), 2⟩
  | (x, y) :: pairs =>
    let nextStart := addIndex start 3
    let out := addIndex start 2
    let head := muxBitCounted start sel x y
    let rest := muxBitsCounted nextStart.value sel pairs
    let code := appendList head.value rest.value.1
    ⟨(code.value, out.value :: rest.value.2),
      nextStart.steps + out.steps + head.steps + rest.steps + code.steps + 2⟩

theorem muxBitsCounted_value {n : ℕ} (start sel : ℕ) (pairs : List (ℕ × ℕ)) :
    (muxBitsCounted (n := n) start sel pairs).value = muxBits start sel pairs := by
  induction pairs generalizing start with
  | nil => rfl
  | cons p ps ih =>
    cases p
    simp only [muxBitsCounted, addIndex_value, muxBitCounted_value, appendList_value, ih, muxBits]

theorem muxBitsCounted_steps {n : ℕ} (start sel : ℕ) (pairs : List (ℕ × ℕ)) :
    (muxBitsCounted (n := n) start sel pairs).steps = 22 * pairs.length + 2 := by
  induction pairs generalizing start with
  | nil => rfl
  | cons p ps ih =>
    cases p
    simp only [muxBitsCounted, addIndex_steps, muxBitCounted_steps, appendList_steps,
      muxBitCounted_value, muxBit_length, ih, List.length_cons]
    omega

def differentBitsFromCounted {n : ℕ} (start : ℕ) :
    List (ℕ × ℕ) → ℕ → Execution (List (CGate n) × ℕ)
  | [], acc => ⟨([], acc), 2⟩
  | (x, y) :: pairs, acc =>
    let nextStart := addIndex start 2
    let nextAcc := addIndex start 1
    let rest := differentBitsFromCounted nextStart.value pairs nextAcc.value
    let code := appendList [.bin Bool.xor x y, .bin Bool.or start acc] rest.value.1
    ⟨(code.value, rest.value.2), nextStart.steps + nextAcc.steps + rest.steps + code.steps + 6⟩

theorem differentBitsFromCounted_value {n : ℕ} (start : ℕ) (pairs : List (ℕ × ℕ)) (acc : ℕ) :
    (differentBitsFromCounted (n := n) start pairs acc).value = differentBitsFrom start pairs acc := by
  induction pairs generalizing start acc with
  | nil => rfl
  | cons p ps ih =>
    cases p
    simp only [differentBitsFromCounted, addIndex_value, appendList_value, ih, differentBitsFrom]

theorem differentBitsFromCounted_steps {n : ℕ} (start : ℕ) (pairs : List (ℕ × ℕ)) (acc : ℕ) :
    (differentBitsFromCounted (n := n) start pairs acc).steps = 14 * pairs.length + 2 := by
  induction pairs generalizing start acc with
  | nil => rfl
  | cons p ps ih =>
    cases p
    simp only [differentBitsFromCounted, addIndex_steps, appendList_steps, ih,
      List.length_cons, List.length_nil]
    omega

def differentBitsCounted {n : ℕ} (start : ℕ) (pairs : List (ℕ × ℕ)) :
    Execution (List (CGate n) × ℕ) :=
  let nextStart := addIndex start 1
  let rest := differentBitsFromCounted nextStart.value pairs start
  ⟨(.cst false :: rest.value.1, rest.value.2), nextStart.steps + rest.steps + 3⟩

theorem differentBitsCounted_value {n : ℕ} (start : ℕ) (pairs : List (ℕ × ℕ)) :
    (differentBitsCounted (n := n) start pairs).value = differentBits start pairs := by
  simp only [differentBitsCounted, addIndex_value, differentBitsFromCounted_value, differentBits]

theorem differentBitsCounted_steps {n : ℕ} (start : ℕ) (pairs : List (ℕ × ℕ)) :
    (differentBitsCounted (n := n) start pairs).steps = 14 * pairs.length + 7 := by
  simp only [differentBitsCounted, addIndex_steps, differentBitsFromCounted_steps]
  omega

def reverseOntoCounted {α : Type*} : List α → List α → Execution (List α)
  | [], acc => ⟨acc, 1⟩
  | x :: xs, acc =>
    let rest := reverseOntoCounted xs (x :: acc)
    ⟨rest.value, rest.steps + 1⟩

theorem reverseOntoCounted_value {α : Type*} (xs acc : List α) :
    (reverseOntoCounted xs acc).value = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp only [reverseOntoCounted, ih, List.reverse_cons, List.append_assoc,
      List.singleton_append]

theorem reverseOntoCounted_steps {α : Type*} (xs acc : List α) :
    (reverseOntoCounted xs acc).steps = xs.length + 1 := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simp only [reverseOntoCounted, ih, List.length_cons]

def restoreWideCounted {n : ℕ} (start : ℕ) (xs ys : List ℕ) (z : ℕ) :
    Execution (List (CGate n) × (ℕ × List ℕ)) :=
  let pairs := zipCounted xs ys
  let sub := subtractBitsCounted start pairs.value z
  let subLen := lengthFrom 0 sub.value.1
  let q := addIndex start subLen.value
  let muxStart := addIndex q.value 1
  let muxPairs := zipCounted sub.value.2.1 xs
  let mux := muxBitsCounted muxStart.value q.value muxPairs.value
  let first := appendList sub.value.1 [.un Bool.not sub.value.2.2]
  let code := appendList first.value mux.value.1
  ⟨(code.value, (q.value, mux.value.2)), pairs.steps + sub.steps + subLen.steps + q.steps +
    muxStart.steps + muxPairs.steps + mux.steps + first.steps + code.steps + 4⟩

theorem restoreWideCounted_value {n : ℕ} (start : ℕ) (xs ys : List ℕ) (z : ℕ) :
    (restoreWideCounted (n := n) start xs ys z).value = restoreWide start xs ys z := by
  simp only [restoreWideCounted, zipCounted_value, subtractBitsCounted_value,
    lengthFrom_value, Nat.zero_add, addIndex_value, muxBitsCounted_value,
    appendList_value, restoreWide]

theorem restoreWideCounted_steps {n : ℕ} (start : ℕ) (xs ys : List ℕ) (z : ℕ)
    (hlen : xs.length = ys.length) :
    (restoreWideCounted (n := n) start xs ys z).steps = 147 * xs.length + 17 := by
  simp only [restoreWideCounted, zipCounted_steps, zipCounted_value, subtractBitsCounted_steps,
    subtractBitsCounted_value, lengthFrom_steps, lengthFrom_value, Nat.zero_add,
    addIndex_steps, muxBitsCounted_steps, appendList_steps, appendList_value,
    List.length_append, List.length_singleton, subtractBits_gate_count,
    subtractBits_word_length, List.length_zip, ← hlen, min_self]
  omega

def restoreLoopCounted {n : ℕ} (start : ℕ) :
    List ℕ → List ℕ → List ℕ → List ℕ → ℕ →
      Execution (List (CGate n) × (List ℕ × List ℕ))
  | [], quot, rem, _, _ => ⟨([], (quot, rem)), 2⟩
  | bit :: bits, quot, rem, den, z =>
    let wideDen := appendList den [z]
    let step := restoreWideCounted start (bit :: rem) wideDen.value z
    let stepLen := lengthFrom 0 step.value.1
    let nextStart := addIndex start stepLen.value
    let remLen := lengthFrom 0 rem
    let nextRem := takeList remLen.value step.value.2.2
    let rest := restoreLoopCounted nextStart.value bits (step.value.2.1 :: quot)
      nextRem.value den z
    let code := appendList step.value.1 rest.value.1
    ⟨(code.value, rest.value.2), wideDen.steps + step.steps + stepLen.steps + nextStart.steps +
      remLen.steps + nextRem.steps + rest.steps + code.steps + 5⟩

theorem restoreLoopCounted_value {n : ℕ} (start : ℕ) (bits quot rem den : List ℕ) (z : ℕ) :
    (restoreLoopCounted (n := n) start bits quot rem den z).value =
      restoreLoop start bits quot rem den z := by
  induction bits generalizing start quot rem with
  | nil => rfl
  | cons bit bits ih =>
    simp only [restoreLoopCounted, appendList_value, restoreWideCounted_value,
      lengthFrom_value, Nat.zero_add, addIndex_value, takeList_value, ih, restoreLoop]

theorem restoreLoopCounted_steps {n : ℕ} (start : ℕ) (bits quot rem den : List ℕ) (z : ℕ)
    (hlen : rem.length = den.length) :
    (restoreLoopCounted (n := n) start bits quot rem den z).steps =
      (195 * rem.length + 223) * bits.length + 2 := by
  induction bits generalizing start quot rem with
  | nil => simp [restoreLoopCounted]
  | cons bit bits ih =>
    have hs : (bit :: rem).length = (den ++ [z]).length := by simp [hlen]
    have hw := restoreWide_word_length (n := n) start (bit :: rem) (den ++ [z]) z hs
    have ht : ((restoreWide (n := n) start (bit :: rem) (den ++ [z]) z).2.2.take
        rem.length).length = rem.length := by rw [List.length_take, hw]; simp
    have hi := ih (start + (restoreWide (n := n) start (bit :: rem) (den ++ [z]) z).1.length)
      ((restoreWide (n := n) start (bit :: rem) (den ++ [z]) z).2.1 :: quot)
      ((restoreWide (n := n) start (bit :: rem) (den ++ [z]) z).2.2.take rem.length)
      (ht.trans hlen)
    rw [ht] at hi
    simp only [restoreWide_gate_count start (bit :: rem) (den ++ [z]) z hs,
      List.length_cons] at hi
    simp only [restoreLoopCounted, appendList_steps, appendList_value, restoreWideCounted_value,
      lengthFrom_steps, lengthFrom_value, Nat.zero_add, addIndex_steps, addIndex_value, takeList_steps,
      takeList_value, hi, restoreWideCounted_steps start (bit :: rem) (den ++ [z]) z hs,
      restoreWide_gate_count start (bit :: rem) (den ++ [z]) z hs, hw, List.length_cons]
    rw [← hlen]
    simp only [Nat.min_eq_left (Nat.le_succ _)]
    ring

def divideWordsCounted {n : ℕ} (start : ℕ) (xs ys : List ℕ) :
    Execution (List (CGate n) × (List ℕ × List ℕ)) :=
  let width := lengthFrom 0 xs
  let zeros := replicateList width.value start
  let reversed := reverseOntoCounted xs []
  let coreStart := addIndex start 1
  let core := restoreLoopCounted coreStart.value reversed.value [] zeros.value ys start
  let coreLen := lengthFrom 0 core.value.1
  let nzStart := addIndex coreStart.value coreLen.value
  let nzPairs := zipCounted ys zeros.value
  let nz := differentBitsCounted nzStart.value nzPairs.value
  let nzLen := lengthFrom 0 nz.value.1
  let maskStart := addIndex nzStart.value nzLen.value
  let maskPairs := zipCounted core.value.2.1 zeros.value
  let mask := muxBitsCounted maskStart.value nz.value.2 maskPairs.value
  let first := appendList [.cst false] core.value.1
  let second := appendList first.value nz.value.1
  let code := appendList second.value mask.value.1
  ⟨(code.value, (mask.value.2, core.value.2.2)), width.steps + zeros.steps + reversed.steps +
    coreStart.steps + core.steps + coreLen.steps + nzStart.steps + nzPairs.steps + nz.steps +
    nzLen.steps + maskStart.steps + maskPairs.steps + mask.steps + first.steps +
    second.steps + code.steps + 4⟩

theorem divideWordsCounted_value {n : ℕ} (start : ℕ) (xs ys : List ℕ) :
    (divideWordsCounted (n := n) start xs ys).value = divideWords start xs ys := by
  simp only [divideWordsCounted, lengthFrom_value, Nat.zero_add, replicateList_value,
    reverseOntoCounted_value, List.append_nil, addIndex_value, restoreLoopCounted_value,
    zipCounted_value, differentBitsCounted_value, muxBitsCounted_value,
    appendList_value, divideWords]

/-- This count includes both copies of the accumulated restoring program in
the final left-associated concatenation. -/
theorem divideWordsCounted_steps {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (divideWordsCounted (n := n) start xs ys).steps =
      250 * xs.length ^ 2 + 335 * xs.length + 36 := by
  have hc := restoreLoop_lengths (n := n) (start + 1) xs.reverse []
    (List.replicate xs.length start) ys start (by simpa only [List.length_replicate] using hlen)
  have hs := restoreLoopCounted_steps (n := n) (start + 1) xs.reverse []
    (List.replicate xs.length start) ys start (by simpa only [List.length_replicate] using hlen)
  simp only [List.length_reverse, List.length_nil, Nat.zero_add, List.length_replicate] at hc hs
  simp only [divideWordsCounted, lengthFrom_value, Nat.zero_add, lengthFrom_steps,
    replicateList_value, replicateList_steps, reverseOntoCounted_steps,
    reverseOntoCounted_value, List.append_nil, addIndex_steps, addIndex_value,
    hs, restoreLoopCounted_value, zipCounted_value, zipCounted_steps,
    differentBitsCounted_value, differentBitsCounted_steps, muxBitsCounted_steps,
    appendList_value, appendList_steps, List.length_append, List.length_singleton,
    differentBits_gate_count, List.length_zip, List.length_replicate,
    hc.1, hc.2.1, ← hlen, min_self]
  ring

theorem divideWordsCounted_steps_le_square {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (divideWordsCounted (n := n) start xs ys).steps ≤ 512 * (xs.length + 1) ^ 2 := by
  rw [divideWordsCounted_steps start xs ys hlen]
  nlinarith [Nat.zero_le (xs.length ^ 2)]

/-- A uniform width-only polynomial, independent of the numerical indices
already stored in the input reference lists. -/
theorem divideWordsCounted_steps_le {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (divideWordsCounted (n := n) start xs ys).steps ≤ 1024 * (xs.length + 1) ^ 4 := by
  calc
    _ ≤ 512 * (xs.length + 1) ^ 2 := divideWordsCounted_steps_le_square start xs ys hlen
    _ ≤ 1024 * (xs.length + 1) ^ 4 := Nat.mul_le_mul (by decide)
      (Nat.pow_le_pow_right (by omega) (by decide))

/-- Numerical quotient and remainder are obtained by executing the exact
emitted circuit, with the existing zero-divisor convention. -/
theorem divideWordsCounted_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (xs ys : List ℕ) (hlen : xs.length = ys.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length) :
    let result := divideWordsCounted (n := n) vals.length xs ys
    let out := runFrom a vals result.value.1
    wordValue out result.value.2.1 = wordValue vals xs / wordValue vals ys ∧
      wordValue out result.value.2.2 = wordValue vals xs % wordValue vals ys := by
  dsimp only
  rw [divideWordsCounted_value]
  exact divideWords_spec a vals xs ys hlen hx hy

example : (subtractBitsCounted (n := 0) 5 [(0, 2), (1, 3)] 4).steps = 164 := by decide

example : (muxBitsCounted (n := 0) 5 4 [(0, 2), (1, 3)]).steps = 46 := by decide

example : (differentBitsCounted (n := 0) 4 [(0, 2), (1, 3)]).steps = 35 := by decide

example : (divideWordsCounted (n := 0) 0 [] []).steps = 36 := by decide

private def divideTwo (x y : List Bool) : ℕ × ℕ × ℕ :=
  let vals := x ++ y
  let compiled := divideWordsCounted (n := 0) 4 [0, 1] [2, 3]
  let out := runFrom (fun i => Fin.elim0 i) vals compiled.value.1
  (wordValue out compiled.value.2.1, wordValue out compiled.value.2.2, compiled.steps)

set_option maxRecDepth 100000 in
example : divideTwo [true, true] [false, true] = (1, 1, 1706) := by decide

set_option maxRecDepth 100000 in
example : divideTwo [true, false] [false, false] = (0, 1, 1706) := by decide

end GodMoveBinaryDivisionCompileCost

#print axioms GodMoveBinaryDivisionCompileCost.fullSubtractCounted_value
#print axioms GodMoveBinaryDivisionCompileCost.fullSubtractCounted_steps
#print axioms GodMoveBinaryDivisionCompileCost.subtractBitsCounted_value
#print axioms GodMoveBinaryDivisionCompileCost.subtractBitsCounted_steps
#print axioms GodMoveBinaryDivisionCompileCost.muxBitsCounted_value
#print axioms GodMoveBinaryDivisionCompileCost.muxBitsCounted_steps
#print axioms GodMoveBinaryDivisionCompileCost.differentBitsCounted_value
#print axioms GodMoveBinaryDivisionCompileCost.differentBitsCounted_steps
#print axioms GodMoveBinaryDivisionCompileCost.reverseOntoCounted_value
#print axioms GodMoveBinaryDivisionCompileCost.restoreWideCounted_value
#print axioms GodMoveBinaryDivisionCompileCost.restoreWideCounted_steps
#print axioms GodMoveBinaryDivisionCompileCost.restoreLoopCounted_value
#print axioms GodMoveBinaryDivisionCompileCost.restoreLoopCounted_steps
#print axioms GodMoveBinaryDivisionCompileCost.divideWordsCounted_value
#print axioms GodMoveBinaryDivisionCompileCost.divideWordsCounted_steps
#print axioms GodMoveBinaryDivisionCompileCost.divideWordsCounted_steps_le_square
#print axioms GodMoveBinaryDivisionCompileCost.divideWordsCounted_steps_le
#print axioms GodMoveBinaryDivisionCompileCost.divideWordsCounted_spec
