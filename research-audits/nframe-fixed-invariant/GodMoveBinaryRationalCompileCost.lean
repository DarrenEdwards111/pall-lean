import GodMoveBinaryNormalizationCompileCost

/-!
# Counted generation of rational multiplication and division

The compiler builds numerator/denominator products, the reciprocal zero guard,
and normalization with the counted binary generators. It also executes counted
length scans, padding, offsets and every code append. Its complete code and
output references erase to the existing canonical rational backend.

These are list and unary-index traversal bounds. Stored natural indices and
immutable tails are shared; counter arithmetic, truth-table lowering, native
allocation and a uniform tape-machine compiler are not included.
-/

namespace GodMoveBinaryRationalCompileCost

open GodMoveBooleanExecutionCost GodMoveBinaryPackingCost
open GodMoveBinaryMultiplyCompileCost GodMoveBinaryNormalizationCompileCost
open GodMoveBinaryMultiply GodMoveBinaryFractionNormalize GodMoveBinaryGCD
open GodMoveBinaryRationalMultiply GodMoveBinaryRationalDivide GodMoveRationalWireEncoding
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

def multiplyFractionsCounted {n : ℕ} (start : ℕ) (x y : FractionRefs) :
    Execution (List (CGate n) × FractionRefs) :=
  let productStart := addIndex start 1
  let pn := productBitsCounted productStart.value start x.numerator y.numerator
  let pnLen := lengthFrom 0 pn.value.1
  let denStart := addIndex productStart.value pnLen.value
  let pd := productBitsCounted denStart.value start x.denominator y.denominator
  let pdLen := lengthFrom 0 pd.value.1
  let sign := addIndex denStart.value pdLen.value
  let normStart := addIndex sign.value 1
  let norm := normalizeWordsCounted normStart.value pn.value.2 pd.value.2
  let first := appendList [.cst false] pn.value.1
  let second := appendList first.value pd.value.1
  let back := appendList [.bin Bool.xor x.sign y.sign] norm.value.1
  let code := appendList second.value back.value
  ⟨(code.value, ⟨sign.value, norm.value.2.1, norm.value.2.2⟩),
    productStart.steps + pn.steps + pnLen.steps + denStart.steps + pd.steps + pdLen.steps +
      sign.steps + normStart.steps + norm.steps + first.steps + second.steps + back.steps +
      code.steps + 8⟩

theorem multiplyFractionsCounted_value {n : ℕ} (start : ℕ) (x y : FractionRefs) :
    (multiplyFractionsCounted (n := n) start x y).value = multiplyFractions start x y := by
  simp only [multiplyFractionsCounted, addIndex_value, productBitsCounted_value,
    lengthFrom_value, Nat.zero_add, normalizeWordsCounted_value, appendList_value,
    multiplyFractions]

theorem multiplyFractionsCounted_steps {n : ℕ} (start : ℕ) (x y : FractionRefs) :
    let pn := productBits (n := n) (start + 1) start x.numerator y.numerator
    let pd := productBits (n := n) (start + 1 + pn.1.length) start x.denominator y.denominator
    (multiplyFractionsCounted (n := n) start x y).steps =
      (productBitsCounted (n := n) (start + 1) start x.numerator y.numerator).steps +
      (productBitsCounted (n := n) (start + 1 + pn.1.length) start x.denominator y.denominator).steps +
      (normalizeWordsCounted (n := n) (start + 1 + pn.1.length + pd.1.length + 1) pn.2 pd.2).steps +
      5 * pn.1.length + 4 * pd.1.length + 24 := by
  dsimp only
  simp only [multiplyFractionsCounted, addIndex_steps, addIndex_value,
    lengthFrom_steps, lengthFrom_value, Nat.zero_add, productBitsCounted_value,
    appendList_steps, appendList_value, List.length_append, List.length_singleton]
  omega

theorem productBitsCounted_steps_le_width {n : ℕ} (start z : ℕ) (xs ys : List ℕ)
    (w : ℕ) (hx : xs.length = w) (hy : ys.length = w) :
    (productBitsCounted (n := n) start z xs ys).steps ≤ 256 * (w + 1) ^ 4 := by
  calc
    _ ≤ 128 * (xs.length + 1) ^ 3 * (ys.length + 2) := productBitsCounted_steps_le start z xs ys
    _ = 128 * (w + 1) ^ 3 * (w + 2) := by rw [hx, hy]
    _ ≤ 128 * (w + 1) ^ 3 * (2 * (w + 1)) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

private theorem product_gates_le_width {n : ℕ} (start z : ℕ) (xs ys : List ℕ)
    (w : ℕ) (hx : xs.length = w) (hy : ys.length = w) :
    (productBits (n := n) start z xs ys).1.length ≤ 12 * (w + 1) ^ 3 := by
  calc
    _ ≤ 6 * xs.length * (xs.length + 1) * (ys.length + 2) := productBits_gate_count_le _ _ _ _
    _ = 6 * w * (w + 1) * (w + 2) := by rw [hx, hy]
    _ ≤ 6 * (w + 1) * (w + 1) * (2 * (w + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))) (by omega)
    _ = _ := by ring

theorem multiplyFractionsCounted_steps_le {n : ℕ} (start : ℕ) (x y : FractionRefs)
    (w : ℕ) (hx : Width x w) (hy : Width y w) :
    (multiplyFractionsCounted (n := n) start x y).steps ≤ 3000000 * (w + 1) ^ 5 := by
  let pn := productBits (n := n) (start + 1) start x.numerator y.numerator
  let pd := productBits (n := n) (start + 1 + pn.1.length) start x.denominator y.denominator
  have hnlen : pn.2.length = 2 * w := by simp only [pn, productBits_word_length, hx.1, hy.1, two_mul]
  have hdlen : pd.2.length = 2 * w := by simp only [pd, productBits_word_length, hx.2, hy.2, two_mul]
  have hn := productBitsCounted_steps_le_width (n := n) (start + 1) start
    x.numerator y.numerator w hx.1 hy.1
  have hd := productBitsCounted_steps_le_width (n := n) (start + 1 + pn.1.length) start
    x.denominator y.denominator w hx.2 hy.2
  have hng := product_gates_le_width (n := n) (start + 1) start x.numerator y.numerator w hx.1 hy.1
  have hdg := product_gates_le_width (n := n) (start + 1 + pn.1.length) start
    x.denominator y.denominator w hx.2 hy.2
  have hm := normalizeWordsCounted_steps_le (n := n)
    (start + 1 + pn.1.length + pd.1.length + 1) pn.2 pd.2 (hnlen.trans hdlen.symm)
  rw [hnlen] at hm
  have hscale : 65536 * (2 * w + 1) ^ 5 ≤ 2097152 * (w + 1) ^ 5 := by
    calc
      _ ≤ 65536 * (2 * (w + 1)) ^ 5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = _ := by ring
  have h35 : (w + 1) ^ 3 ≤ (w + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h45 : (w + 1) ^ 4 ≤ (w + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h5 : 1 ≤ (w + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  change pn.1.length ≤ _ at hng
  change pd.1.length ≤ _ at hdg
  rw [multiplyFractionsCounted_steps]
  change (productBitsCounted (n := n) (start + 1) start x.numerator y.numerator).steps +
    (productBitsCounted (n := n) (start + 1 + pn.1.length) start x.denominator y.denominator).steps +
    (normalizeWordsCounted (n := n) (start + 1 + pn.1.length + pd.1.length + 1) pn.2 pd.2).steps +
    5 * pn.1.length + 4 * pd.1.length + 24 ≤ _
  omega

def oneWordCounted (start width : ℕ) : Execution (List ℕ) :=
  let one := addIndex start 1
  let zeros := replicateList width start
  let word := takeList width (one.value :: zeros.value)
  ⟨word.value, one.steps + zeros.steps + word.steps + 1⟩

theorem oneWordCounted_value (start width : ℕ) :
    (oneWordCounted start width).value = oneWord start width := by
  simp only [oneWordCounted, addIndex_value, replicateList_value, takeList_value, oneWord]

theorem oneWordCounted_steps (start width : ℕ) :
    (oneWordCounted start width).steps = 2 * width + 5 := by
  simp only [oneWordCounted, addIndex_steps, replicateList_steps, takeList_steps,
    List.length_cons, replicateList_value, List.length_replicate, Nat.min_eq_left (Nat.le_succ _)]
  omega

def reciprocalFractionCounted {n : ℕ} (start : ℕ) (x : FractionRefs) :
    Execution (List (CGate n) × FractionRefs) :=
  let width := lengthFrom 0 x.numerator
  let zeros := replicateList width.value start
  let nzStart := addIndex start 2
  let nz := nonzeroWordCounted nzStart.value x.numerator
  let nzLen := lengthFrom 0 nz.value.1
  let numStart := addIndex nzStart.value nzLen.value
  let num := chooseWordsCounted numStart.value nz.value.2 x.denominator zeros.value
  let numLen := lengthFrom 0 num.value.1
  let denStart := addIndex numStart.value numLen.value
  let ones := oneWordCounted start width.value
  let den := chooseWordsCounted denStart.value nz.value.2 x.numerator ones.value
  let first := appendList [.cst false, .cst true] nz.value.1
  let second := appendList first.value num.value.1
  let code := appendList second.value den.value.1
  ⟨(code.value, ⟨x.sign, num.value.2, den.value.2⟩),
    width.steps + zeros.steps + nzStart.steps + nz.steps + nzLen.steps + numStart.steps +
      num.steps + numLen.steps + denStart.steps + ones.steps + den.steps + first.steps +
      second.steps + code.steps + 7⟩

theorem reciprocalFractionCounted_value {n : ℕ} (start : ℕ) (x : FractionRefs) :
    (reciprocalFractionCounted (n := n) start x).value = reciprocalFraction start x := by
  simp only [reciprocalFractionCounted, lengthFrom_value, Nat.zero_add, replicateList_value,
    addIndex_value, nonzeroWordCounted_value, chooseWordsCounted_value, oneWordCounted_value,
    appendList_value, reciprocalFraction]

theorem reciprocalFractionCounted_steps_le_linear {n : ℕ} (start : ℕ) (x : FractionRefs)
    (w : ℕ) (hx : Width x w) :
    (reciprocalFractionCounted (n := n) start x).steps ≤ 512 * (w + 1) := by
  let nz := nonzeroWord (n := n) (start + 2) x.numerator
  let num := chooseWords (n := n) (start + 2 + nz.1.length) nz.2 x.denominator
    (List.replicate x.numerator.length start)
  have hnz := nonzeroWordCounted_steps_le (n := n) (start + 2) x.numerator
  have hn := chooseWordsCounted_steps_le (n := n) (start + 2 + nz.1.length) nz.2 x.denominator
    (List.replicate x.numerator.length start)
  have hd := chooseWordsCounted_steps_le (n := n) (start + 2 + nz.1.length + num.1.length) nz.2
    x.numerator (oneWord start x.numerator.length)
  have hnlen : x.denominator.length = (List.replicate x.numerator.length start).length := by
    simp only [List.length_replicate, hx.1, hx.2]
  have hzlen : nz.1.length = 2 * w + 2 := by simp only [nz, nonzeroWord_gate_count, hx.1]
  have humlen : num.1.length = 3 * w := by
    dsimp only [num]
    rw [chooseWords_gate_count _ _ _ _ hnlen, hx.2]
  have hxn := hx.1
  have hxd := hx.2
  simp only [reciprocalFractionCounted, lengthFrom_value, Nat.zero_add, lengthFrom_steps,
    replicateList_steps, replicateList_value, addIndex_steps, addIndex_value,
    nonzeroWordCounted_value, chooseWordsCounted_value, oneWordCounted_value,
    oneWordCounted_steps, appendList_steps, appendList_value,
    List.length_append, List.length_cons, List.length_nil]
  change (2 * x.numerator.length + 1) + (x.numerator.length + 1) + 3 +
    (nonzeroWordCounted (n := n) (start + 2) x.numerator).steps + (2 * nz.1.length + 1) +
    (nz.1.length + 1) +
    (chooseWordsCounted (n := n) (start + 2 + nz.1.length) nz.2 x.denominator
      (List.replicate x.numerator.length start)).steps + (2 * num.1.length + 1) +
    (num.1.length + 1) + (2 * x.numerator.length + 5) +
    (chooseWordsCounted (n := n) (start + 2 + nz.1.length + num.1.length) nz.2
      x.numerator (oneWord start x.numerator.length)).steps + 3 +
    (2 + nz.1.length + 1) + (2 + nz.1.length + num.1.length + 1) + 7 ≤ _
  omega

theorem reciprocalFractionCounted_steps_le {n : ℕ} (start : ℕ) (x : FractionRefs)
    (w : ℕ) (hx : Width x w) :
    (reciprocalFractionCounted (n := n) start x).steps ≤ 1024 * (w + 1) ^ 2 := by
  have h := reciprocalFractionCounted_steps_le_linear (n := n) start x w hx
  nlinarith [Nat.zero_le (w ^ 2)]

def divideFractionsCounted {n : ℕ} (start : ℕ) (x y : FractionRefs) :
    Execution (List (CGate n) × FractionRefs) :=
  let inv := reciprocalFractionCounted start y
  let invLen := lengthFrom 0 inv.value.1
  let productStart := addIndex start invLen.value
  let product := multiplyFractionsCounted productStart.value x inv.value.2
  let code := appendList inv.value.1 product.value.1
  ⟨(code.value, product.value.2), inv.steps + invLen.steps + productStart.steps +
    product.steps + code.steps + 1⟩

theorem divideFractionsCounted_value {n : ℕ} (start : ℕ) (x y : FractionRefs) :
    (divideFractionsCounted (n := n) start x y).value = divideFractions start x y := by
  simp only [divideFractionsCounted, reciprocalFractionCounted_value, lengthFrom_value,
    Nat.zero_add, addIndex_value, multiplyFractionsCounted_value, appendList_value, divideFractions]

theorem divideFractionsCounted_steps_le {n : ℕ} (start : ℕ) (x y : FractionRefs)
    (w : ℕ) (hx : Width x w) (hy : Width y w) :
    (divideFractionsCounted (n := n) start x y).steps ≤ 4000000 * (w + 1) ^ 5 := by
  let inv := reciprocalFraction (n := n) start y
  have hi := reciprocalFractionCounted_steps_le_linear (n := n) start y w hy
  have hg := reciprocalFraction_gate_count (n := n) start y w hy
  have hm := multiplyFractionsCounted_steps_le (n := n) (start + inv.1.length) x inv.2 w hx
    (reciprocalFraction_width start y w hy)
  have h15 : w + 1 ≤ (w + 1) ^ 5 := by
    calc
      _ = (w + 1) ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  have h5 : 1 ≤ (w + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
  simp only [divideFractionsCounted, lengthFrom_steps, lengthFrom_value, Nat.zero_add,
    addIndex_steps, addIndex_value, reciprocalFractionCounted_value, appendList_steps]
  change (reciprocalFractionCounted (n := n) start y).steps + (2 * inv.1.length + 1) +
    (inv.1.length + 1) + (multiplyFractionsCounted (n := n) (start + inv.1.length) x inv.2).steps +
    (inv.1.length + 1) + 1 ≤ _
  change inv.1.length = _ at hg
  omega

theorem multiplyFractionsCounted_represents {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (x y : FractionRefs) (q r : ℚ) (w : ℕ) (hxw : Width x w) (hyw : Width y w)
    (hxv : Valid x vals.length) (hyv : Valid y vals.length)
    (hx : Represents vals x q) (hy : Represents vals y r) :
    Represents (runFrom a vals (multiplyFractionsCounted vals.length x y).value.1)
      (multiplyFractionsCounted (n := n) vals.length x y).value.2 (q * r) := by
  rw [multiplyFractionsCounted_value]
  exact multiplyFractions_represents a vals x y q r w hxw hyw hxv hyv hx hy

theorem reciprocalFractionCounted_represents {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (x : FractionRefs) (q : ℚ) (w : ℕ) (hxw : Width x w)
    (hxv : Valid x vals.length) (hx : Represents vals x q) :
    Represents (runFrom a vals (reciprocalFractionCounted vals.length x).value.1)
      (reciprocalFractionCounted (n := n) vals.length x).value.2 q⁻¹ := by
  rw [reciprocalFractionCounted_value]
  exact reciprocalFraction_represents a vals x q w hxw hxv hx

theorem divideFractionsCounted_represents {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (x y : FractionRefs) (q r : ℚ) (w : ℕ) (hxw : Width x w) (hyw : Width y w)
    (hxv : Valid x vals.length) (hyv : Valid y vals.length)
    (hx : Represents vals x q) (hy : Represents vals y r) :
    Represents (runFrom a vals (divideFractionsCounted vals.length x y).value.1)
      (divideFractionsCounted (n := n) vals.length x y).value.2 (q / r) := by
  rw [divideFractionsCounted_value]
  exact divideFractions_represents a vals x y q r w hxw hyw hxv hyv hx hy

example : (oneWordCounted 3 2).value = [4, 3] ∧ (oneWordCounted 3 2).steps = 9 := by decide

private def reciprocalTwo (negative : Bool) (num den : List Bool) : ℤ × ℕ :=
  let vals := negative :: (num ++ den)
  let refs : FractionRefs := ⟨0, [1, 2], [3, 4]⟩
  let compiled := reciprocalFractionCounted (n := 0) 5 refs
  let out := runFrom (fun i => Fin.elim0 i) vals compiled.value.1
  (signedValue out compiled.value.2.sign compiled.value.2.numerator,
    GodMoveBinaryAdder.wordValue out compiled.value.2.denominator)

set_option maxRecDepth 100000 in
example : reciprocalTwo true [true, false] [false, true] = (-2, 1) := by decide

set_option maxRecDepth 100000 in
example : reciprocalTwo true [false, false] [true, false] = (0, 1) := by decide

private def multiplyOne : ℤ × ℕ :=
  let vals := [true, true, true, false, true, true]
  let x : FractionRefs := ⟨0, [1], [2]⟩
  let y : FractionRefs := ⟨3, [4], [5]⟩
  let compiled := multiplyFractionsCounted (n := 0) 6 x y
  let out := runFrom (fun i => Fin.elim0 i) vals compiled.value.1
  (signedValue out compiled.value.2.sign compiled.value.2.numerator,
    GodMoveBinaryAdder.wordValue out compiled.value.2.denominator)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
example : multiplyOne = (-1, 1) := by decide

end GodMoveBinaryRationalCompileCost

#print axioms GodMoveBinaryRationalCompileCost.multiplyFractionsCounted_value
#print axioms GodMoveBinaryRationalCompileCost.multiplyFractionsCounted_steps
#print axioms GodMoveBinaryRationalCompileCost.productBitsCounted_steps_le_width
#print axioms GodMoveBinaryRationalCompileCost.multiplyFractionsCounted_steps_le
#print axioms GodMoveBinaryRationalCompileCost.oneWordCounted_value
#print axioms GodMoveBinaryRationalCompileCost.oneWordCounted_steps
#print axioms GodMoveBinaryRationalCompileCost.reciprocalFractionCounted_value
#print axioms GodMoveBinaryRationalCompileCost.reciprocalFractionCounted_steps_le_linear
#print axioms GodMoveBinaryRationalCompileCost.reciprocalFractionCounted_steps_le
#print axioms GodMoveBinaryRationalCompileCost.divideFractionsCounted_value
#print axioms GodMoveBinaryRationalCompileCost.divideFractionsCounted_steps_le
#print axioms GodMoveBinaryRationalCompileCost.multiplyFractionsCounted_represents
#print axioms GodMoveBinaryRationalCompileCost.reciprocalFractionCounted_represents
#print axioms GodMoveBinaryRationalCompileCost.divideFractionsCounted_represents
