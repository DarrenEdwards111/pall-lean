import GodMoveWireSum
import GodMoveBinarySubtract

/-!
# Multiplication of two variable binary words

Both operands are wire references, not compile-time coefficients. Each round
forms a controlled copy of the second word and adds it to twice the recursive
product. Padding retains all carries. The emitted Boolean gate count is
polynomial in the two input widths; no integer multiplication primitive is
used by the generated circuit.
-/

namespace GodMoveBinaryMultiply

open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer
open GodMoveBinaryAdder GodMoveControlledWord GodMoveSignedBinary GodMoveWireSum

def maskWord {n : ℕ} (start selector : ℕ) (word : List ℕ) : List (CGate n) × List ℕ :=
  (word.map (fun i => .bin Bool.and selector i), List.range' start word.length)

@[simp] theorem maskWord_gate_count {n : ℕ} (start selector : ℕ) (word : List ℕ) :
    (maskWord (n := n) start selector word).1.length = word.length := by simp [maskWord]

@[simp] theorem maskWord_word_length {n : ℕ} (start selector : ℕ) (word : List ℕ) :
    (maskWord (n := n) start selector word).2.length = word.length := by simp [maskWord]

theorem maskWord_refs_lt {n : ℕ} (start selector : ℕ) (word : List ℕ) :
    ∀ i ∈ (maskWord (n := n) start selector word).2, i < start + word.length := by
  intro i hi
  have h := List.mem_range'.mp hi
  omega

theorem maskWord_runFrom {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (start selector : ℕ) (word : List ℕ) (hs : selector < vals.length)
    (hw : ∀ i ∈ word, i < vals.length) :
    runFrom a vals (maskWord (n := n) start selector word).1 =
      vals ++ word.map (fun i => vals.getD selector false && vals.getD i false) := by
  unfold maskWord
  induction word generalizing vals with
  | nil => simp [runFrom]
  | cons i is ih =>
    have ht : ∀ j ∈ is, j < vals.length := fun j hj => hw j (by simp [hj])
    simp only [List.map_cons, runFrom, evalGate]
    have hs' : selector < (vals ++ [vals.getD selector false && vals.getD i false]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hs' (fun j hj => by
      simp only [List.length_append, List.length_singleton]; exact (ht j hj).trans_le (by omega))]
    rw [List.getD_append _ _ _ _ hs]
    have he : is.map (fun j => vals.getD selector false &&
        (vals ++ [vals.getD selector false && vals.getD i false]).getD j false) =
        is.map (fun j => vals.getD selector false && vals.getD j false) := by
      apply List.map_congr_left
      intro j hj
      rw [List.getD_append _ _ _ _ (ht j hj)]
    rw [he]
    simp only [List.append_assoc, List.singleton_append]

theorem bitsValue_readWord (vals : List Bool) (word : List ℕ) :
    bitsValue (word.map (fun i => vals.getD i false)) = wordValue vals word := by
  induction word with
  | nil => rfl
  | cons i is ih => simp only [List.map_cons, bitsValue, wordValue, ih]

theorem maskWord_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (selector : ℕ) (word : List ℕ) (hs : selector < vals.length)
    (hw : ∀ i ∈ word, i < vals.length) :
    wordValue (runFrom a vals (maskWord (n := n) vals.length selector word).1)
      (maskWord (n := n) vals.length selector word).2 =
      (vals.getD selector false).toNat * wordValue vals word := by
  rw [maskWord_runFrom a vals vals.length selector word hs hw]
  change wordValue
    (vals ++ word.map (fun i => vals.getD selector false && vals.getD i false))
    (List.range' vals.length word.length) = _
  rw [← List.length_map (f := fun i => vals.getD selector false && vals.getD i false)
    (as := word), wordValue_range_append]
  rw [show word.map (fun i => vals.getD selector false && vals.getD i false) =
    (word.map (fun i => vals.getD i false)).map (fun b => vals.getD selector false && b) by
      simp only [List.map_map, Function.comp_def]]
  rw [bitsValue_mask, bitsValue_readWord]
  cases vals.getD selector false <;> simp

def multiplyBits {n : ℕ} (start zeroRef : ℕ) : List ℕ → List ℕ → List (CGate n) × List ℕ
  | [], _ => ([], [])
  | x :: xs, ys =>
    let rest := multiplyBits start zeroRef xs ys
    let masked := maskWord (start + rest.1.length) x ys
    let addition := addBits (start + rest.1.length + masked.1.length)
      (paddedPairs zeroRef (zeroRef :: rest.2) masked.2) zeroRef
    ((rest.1 ++ masked.1) ++ addition.1, addition.2)

theorem multiplyBits_word_length {n : ℕ} (start zeroRef : ℕ) (xs ys : List ℕ) :
    (multiplyBits (n := n) start zeroRef xs ys).2.length = xs.length * (ys.length + 2) := by
  induction xs with
  | nil => simp [multiplyBits]
  | cons x xs ih =>
    simp only [multiplyBits, addBits_word_length, paddedPairs_length,
      List.length_cons, maskWord_word_length, ih]
    ring

theorem multiplyBits_gate_count_le {n : ℕ} (start zeroRef : ℕ) (xs ys : List ℕ) :
    (multiplyBits (n := n) start zeroRef xs ys).1.length ≤
      6 * xs.length * (xs.length + 1) * (ys.length + 2) := by
  induction xs with
  | nil => simp [multiplyBits]
  | cons x xs ih =>
    simp only [multiplyBits, List.length_append, maskWord_gate_count,
      addBits_gate_count, paddedPairs_length, List.length_cons,
      multiplyBits_word_length, maskWord_word_length]
    nlinarith [Nat.zero_le (xs.length * ys.length)]

theorem multiplyBits_refs_lt {n : ℕ} (start zeroRef : ℕ) (xs ys : List ℕ)
    (hz : zeroRef < start) : ∀ i ∈ (multiplyBits (n := n) start zeroRef xs ys).2,
      i < start + (multiplyBits (n := n) start zeroRef xs ys).1.length := by
  cases xs with
  | nil => simp [multiplyBits]
  | cons x xs =>
    intro i hi
    have h := addBits_refs_lt (n := n)
      (start + (multiplyBits (n := n) start zeroRef xs ys).1.length +
        (maskWord (n := n) (start + (multiplyBits (n := n) start zeroRef xs ys).1.length) x ys).1.length)
      (paddedPairs zeroRef (zeroRef :: (multiplyBits (n := n) start zeroRef xs ys).2)
        (maskWord (n := n) (start + (multiplyBits (n := n) start zeroRef xs ys).1.length) x ys).2)
      zeroRef (by omega) i hi
    simpa only [multiplyBits, List.length_append, addBits_gate_count, Nat.add_assoc] using h

/-- Exact multiplication for arbitrary input words, allowing shared references.
The false wire is an ordinary earlier wire, and every final carry is retained. -/
theorem multiplyBits_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (zeroRef : ℕ) (xs ys : List ℕ) (hz : zeroRef < vals.length)
    (hzval : vals.getD zeroRef false = false)
    (hxs : ∀ i ∈ xs, i < vals.length) (hys : ∀ i ∈ ys, i < vals.length) :
    wordValue (runFrom a vals (multiplyBits (n := n) vals.length zeroRef xs ys).1)
      (multiplyBits (n := n) vals.length zeroRef xs ys).2 =
      wordValue vals xs * wordValue vals ys := by
  induction xs with
  | nil => simp [multiplyBits, wordValue]
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have hxt : ∀ i ∈ xs, i < vals.length := fun i hi => hxs i (by simp [hi])
    have hrest := ih hxt
    let rest := multiplyBits (n := n) vals.length zeroRef xs ys
    let rv := runFrom a vals rest.1
    have hrvlen : rv.length = vals.length + rest.1.length := runFrom_length _ _ _
    let masked := maskWord (n := n) rv.length x ys
    let cv := runFrom a rv masked.1
    have hcvlen : cv.length = rv.length + masked.1.length := runFrom_length _ _ _
    have hzeroRV : zeroRef < rv.length := by rw [hrvlen]; omega
    have hzeroCV : zeroRef < cv.length := by rw [hcvlen]; omega
    have hzeroRVval : rv.getD zeroRef false = false :=
      (read_runFrom_old a vals rest.1 zeroRef hz).trans hzval
    have hzeroCVval : cv.getD zeroRef false = false :=
      (read_runFrom_old a rv masked.1 zeroRef hzeroRV).trans hzeroRVval
    have hrestrefs : ∀ i ∈ rest.2, i < rv.length := by
      rw [hrvlen]
      exact multiplyBits_refs_lt vals.length zeroRef xs ys hz
    have hmaskedrefs : ∀ i ∈ masked.2, i < cv.length := by
      rw [hcvlen, show masked.1.length = ys.length from maskWord_gate_count _ _ _]
      exact maskWord_refs_lt rv.length x ys
    have hshiftrefs : ∀ i ∈ zeroRef :: rest.2, i < cv.length := by
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hzeroCV
      · exact (hrestrefs i hi).trans_le (by rw [hcvlen]; omega)
    have hpairs := paddedPairs_refs zeroRef cv.length (zeroRef :: rest.2) masked.2
      hzeroCV hshiftrefs hmaskedrefs
    have hadd := addBits_spec a cv (paddedPairs zeroRef (zeroRef :: rest.2) masked.2)
      zeroRef hpairs hzeroCV
    rw [(paddedPairs_values cv zeroRef (zeroRef :: rest.2) masked.2 hzeroCVval).1,
      (paddedPairs_values cv zeroRef (zeroRef :: rest.2) masked.2 hzeroCVval).2,
      hzeroCVval] at hadd
    have hrvalue : wordValue cv rest.2 = wordValue vals xs * wordValue vals ys := by
      rw [wordValue_runFrom_old a rv masked.1 rest.2 hrestrefs]
      exact hrest
    have hmvalue : wordValue cv masked.2 =
        (vals.getD x false).toNat * wordValue vals ys := by
      have hmask := maskWord_spec a rv x ys (by rw [hrvlen]; omega)
        (fun i hi => (hys i hi).trans_le (by rw [hrvlen]; omega))
      change wordValue cv masked.2 = _ at hmask
      rw [read_runFrom_old a vals rest.1 x hx,
        wordValue_runFrom_old a vals rest.1 ys hys] at hmask
      exact hmask
    simp only [wordValue, hzeroCVval, Bool.toNat_false, Nat.zero_add,
      hrvalue, hmvalue, Nat.add_zero] at hadd
    change wordValue
      (runFrom a vals ((rest.1 ++
        (maskWord (n := n) (vals.length + rest.1.length) x ys).1) ++
        (addBits (n := n) (vals.length + rest.1.length +
          (maskWord (n := n) (vals.length + rest.1.length) x ys).1.length)
          (paddedPairs zeroRef (zeroRef :: rest.2)
            (maskWord (n := n) (vals.length + rest.1.length) x ys).2) zeroRef).1))
      (addBits (n := n) (vals.length + rest.1.length +
        (maskWord (n := n) (vals.length + rest.1.length) x ys).1.length)
        (paddedPairs zeroRef (zeroRef :: rest.2)
          (maskWord (n := n) (vals.length + rest.1.length) x ys).2) zeroRef).2 = _
    rw [← hrvlen]
    change wordValue
      (runFrom a vals ((rest.1 ++ masked.1) ++
        (addBits (n := n) (rv.length + masked.1.length)
          (paddedPairs zeroRef (zeroRef :: rest.2) masked.2) zeroRef).1))
      (addBits (n := n) (rv.length + masked.1.length)
        (paddedPairs zeroRef (zeroRef :: rest.2) masked.2) zeroRef).2 = _
    rw [← hcvlen, runFrom_append, runFrom_append]
    rw [hadd]
    simp only [wordValue]
    ring

/-- Dropping high zero bits preserves a word whose value fits the requested
width. This is about the actual referenced bits, without a supplied bit table. -/
theorem wordValue_take_eq_of_lt (vals : List Bool) (word : List ℕ) (width : ℕ)
    (h : wordValue vals word < 2 ^ width) :
    wordValue vals (word.take width) = wordValue vals word := by
  induction width generalizing word with
  | zero =>
    simp only [pow_zero] at h
    have he : wordValue vals word = 0 := by omega
    simp [he, wordValue]
  | succ width ih =>
    cases word with
    | nil => rfl
    | cons i is =>
      have ht : wordValue vals is < 2 ^ width := by
        simp only [wordValue, pow_succ] at h
        omega
      simp only [List.take_succ_cons, wordValue, ih is ht]

/-- Keep just the mathematically sufficient product width after generating
the carry-preserving multiplication circuit. No gate depends on this trimming. -/
def productBits {n : ℕ} (start zeroRef : ℕ) (xs ys : List ℕ) : List (CGate n) × List ℕ :=
  let code := multiplyBits start zeroRef xs ys
  (code.1, (code.2 ++ List.replicate (xs.length + ys.length) zeroRef).take
    (xs.length + ys.length))

theorem productBits_gate_count_le {n : ℕ} (start zeroRef : ℕ) (xs ys : List ℕ) :
    (productBits (n := n) start zeroRef xs ys).1.length ≤
      6 * xs.length * (xs.length + 1) * (ys.length + 2) :=
  multiplyBits_gate_count_le start zeroRef xs ys

theorem productBits_word_length {n : ℕ} (start zeroRef : ℕ) (xs ys : List ℕ) :
    (productBits (n := n) start zeroRef xs ys).2.length = xs.length + ys.length := by
  simp only [productBits, List.length_take, List.length_append, List.length_replicate]
  exact Nat.min_eq_left (Nat.le_add_left _ _)

theorem productBits_refs_lt {n : ℕ} (start zeroRef : ℕ) (xs ys : List ℕ)
    (hz : zeroRef < start) : ∀ i ∈ (productBits (n := n) start zeroRef xs ys).2,
      i < start + (productBits (n := n) start zeroRef xs ys).1.length := by
  intro i hi
  have hm := List.mem_of_mem_take hi
  rcases List.mem_append.mp hm with hm | hm
  · exact multiplyBits_refs_lt start zeroRef xs ys hz i hm
  · have he := List.eq_of_mem_replicate hm
    subst i
    exact hz.trans_le (Nat.le_add_right _ _)

theorem productBits_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (zeroRef : ℕ) (xs ys : List ℕ) (hz : zeroRef < vals.length)
    (hzval : vals.getD zeroRef false = false)
    (hxs : ∀ i ∈ xs, i < vals.length) (hys : ∀ i ∈ ys, i < vals.length) :
    wordValue (runFrom a vals (productBits (n := n) vals.length zeroRef xs ys).1)
      (productBits (n := n) vals.length zeroRef xs ys).2 =
      wordValue vals xs * wordValue vals ys := by
  have he := multiplyBits_spec a vals zeroRef xs ys hz hzval hxs hys
  have hfit : wordValue vals xs * wordValue vals ys < 2 ^ (xs.length + ys.length) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt
      (GodMoveBinarySubtract.wordValue_lt_two_pow_length vals xs)
      (GodMoveBinarySubtract.wordValue_lt_two_pow_length vals ys)
  have hzout : (runFrom a vals (multiplyBits (n := n) vals.length zeroRef xs ys).1).getD
      zeroRef false = false := (read_runFrom_old a vals _ zeroRef hz).trans hzval
  have hpad := wordValue_pad_zero
    (runFrom a vals (multiplyBits (n := n) vals.length zeroRef xs ys).1)
    (multiplyBits (n := n) vals.length zeroRef xs ys).2 zeroRef
    (xs.length + ys.length) hzout
  have he' := hpad.trans he
  unfold productBits
  rw [wordValue_take_eq_of_lt _ _ _ (he' ▸ hfit)]
  exact he'

private def multiplyExample (x y : List Bool) : ℕ :=
  let vals := x ++ y ++ [false]
  let code := productBits (n := 0) vals.length (x.length + y.length)
    (List.range x.length) (List.range' x.length y.length)
  wordValue (runFrom (fun i => Fin.elim0 i) vals code.1) code.2

set_option maxRecDepth 2048 in
example : multiplyExample [false, true] [true, true] = 6 := by decide
set_option maxRecDepth 2048 in
example : multiplyExample [true, true] [true, true] = 9 := by decide
example : multiplyExample [] [true, true] = 0 := by decide

end GodMoveBinaryMultiply

#print axioms GodMoveBinaryMultiply.maskWord_spec
#print axioms GodMoveBinaryMultiply.multiplyBits_word_length
#print axioms GodMoveBinaryMultiply.multiplyBits_gate_count_le
#print axioms GodMoveBinaryMultiply.multiplyBits_refs_lt
#print axioms GodMoveBinaryMultiply.multiplyBits_spec
#print axioms GodMoveBinaryMultiply.wordValue_take_eq_of_lt
#print axioms GodMoveBinaryMultiply.productBits_gate_count_le
#print axioms GodMoveBinaryMultiply.productBits_word_length
#print axioms GodMoveBinaryMultiply.productBits_refs_lt
#print axioms GodMoveBinaryMultiply.productBits_spec
