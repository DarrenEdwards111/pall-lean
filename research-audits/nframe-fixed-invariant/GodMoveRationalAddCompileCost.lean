import GodMoveSignedArithmeticCompileCost
import GodMoveBinaryNormalizationCompileCost
import GodMoveBinaryRationalAdd

/-!
# Counted generation of canonical rational addition and subtraction

The executable compiler constructs three cross-product circuits, the selected
signed arithmetic circuit and the normalizer using counted builders. Its
counter includes every variable-sized code copy, width traversal, index offset
and padding operation. Exact erasure concerns the entire code and output
references, not merely their dimensions. The shared-index/list traversal model
does not identify this counter with native execution or tape-machine steps.
-/

namespace GodMoveRationalAddCompileCost

open GodMoveBooleanExecutionCost GodMoveBinaryPackingCost
open GodMoveBinaryMultiplyCompileCost GodMoveSignedArithmeticCompileCost
open GodMoveBinaryNormalizationCompileCost GodMoveBinaryRationalAdd
open GodMoveBinaryMultiply GodMoveSignedArithmetic GodMoveBinaryFractionNormalize
open GodMoveRationalWireEncoding
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

def crossProductsCounted {n : ℕ} (start : ℕ) (x y : FractionRefs) :
    Execution (List (CGate n) × CrossRefs) :=
  let ls := addIndex start 1
  let l := productBitsCounted ls.value start x.numerator y.denominator
  let ll := lengthFrom 0 l.value.1
  let rs := addIndex ls.value ll.value
  let r := productBitsCounted rs.value start y.numerator x.denominator
  let rl := lengthFrom 0 r.value.1
  let ds := addIndex rs.value rl.value
  let d := productBitsCounted ds.value start x.denominator y.denominator
  let c0 := appendList [.cst false] l.value.1
  let c1 := appendList c0.value r.value.1
  let code := appendList c1.value d.value.1
  ⟨(code.value, ⟨l.value.2, r.value.2, d.value.2⟩),
    ls.steps + l.steps + ll.steps + rs.steps + r.steps + rl.steps + ds.steps +
      d.steps + c0.steps + c1.steps + code.steps + 5⟩

theorem crossProductsCounted_value {n : ℕ} (start : ℕ) (x y : FractionRefs) :
    (crossProductsCounted (n := n) start x y).value = crossProducts start x y := by
  simp only [crossProductsCounted, addIndex_value, productBitsCounted_value,
    lengthFrom_value, Nat.zero_add, appendList_value, crossProducts]

private theorem product_steps_width {n : ℕ} (start z : ℕ) (xs ys : List ℕ) (w : ℕ)
    (hx : xs.length = w) (hy : ys.length = w) :
    (productBitsCounted (n := n) start z xs ys).steps ≤ 256 * (w + 1) ^ 4 := by
  have h := productBitsCounted_steps_le (n := n) start z xs ys
  rw [hx, hy] at h
  calc
    _ ≤ 128 * (w + 1) ^ 3 * (w + 2) := h
    _ ≤ 128 * (w + 1) ^ 3 * (2 * (w + 1)) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

private theorem product_gates_width {n : ℕ} (start z : ℕ) (xs ys : List ℕ) (w : ℕ)
    (hx : xs.length = w) (hy : ys.length = w) :
    (productBits (n := n) start z xs ys).1.length ≤ 12 * (w + 1) ^ 3 := by
  have h := productBits_gate_count_le (n := n) start z xs ys
  rw [hx, hy] at h
  calc
    _ ≤ 6 * w * (w + 1) * (w + 2) := h
    _ ≤ 6 * (w + 1) * (w + 1) * (2 * (w + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))) (by omega)
    _ = _ := by ring

theorem crossProductsCounted_steps_le {n : ℕ} (start : ℕ) (x y : FractionRefs)
    (w : ℕ) (hx : Width x w) (hy : Width y w) :
    (crossProductsCounted (n := n) start x y).steps ≤ 1024 * (w + 1) ^ 4 := by
  let l := productBits (n := n) (start + 1) start x.numerator y.denominator
  let r := productBits (n := n) (start + 1 + l.1.length) start y.numerator x.denominator
  have hl := product_steps_width (n := n) (start + 1) start x.numerator y.denominator w hx.1 hy.2
  have hr := product_steps_width (n := n) (start + 1 + l.1.length) start y.numerator x.denominator w hy.1 hx.2
  have hd := product_steps_width (n := n) (start + 1 + l.1.length + r.1.length) start x.denominator y.denominator w hx.2 hy.2
  have hgl := product_gates_width (n := n) (start + 1) start x.numerator y.denominator w hx.1 hy.2
  have hgr := product_gates_width (n := n) (start + 1 + l.1.length) start y.numerator x.denominator w hy.1 hx.2
  change l.1.length ≤ _ at hgl
  change r.1.length ≤ _ at hgr
  have h34 : (w + 1) ^ 3 ≤ (w + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h04 : 1 ≤ (w + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  simp only [crossProductsCounted, addIndex_steps, addIndex_value, lengthFrom_steps,
    lengthFrom_value, Nat.zero_add, appendList_steps, appendList_value,
    productBitsCounted_value, List.length_append, List.length_singleton]
  change _ + _ + (2 * l.1.length + 1) + (l.1.length + 1) + _ +
    (2 * r.1.length + 1) + (r.1.length + 1) + _ + _ + _ + _ + _ ≤ _
  dsimp only [l, r] at *
  omega

def combineSignedCounted {n : ℕ} (subtract : Bool) (start sx : ℕ)
    (xs : List ℕ) (sy : ℕ) (ys : List ℕ) : Execution (List (CGate n) × (ℕ × List ℕ)) :=
  let result := if subtract then subtractSignedCounted start sx xs sy ys
    else addSignedCounted start sx xs sy ys
  ⟨result.value, result.steps + 1⟩

theorem combineSignedCounted_value {n : ℕ} (subtract : Bool) (start sx : ℕ)
    (xs : List ℕ) (sy : ℕ) (ys : List ℕ) :
    (combineSignedCounted (n := n) subtract start sx xs sy ys).value =
      combineSigned subtract start sx xs sy ys := by
  cases subtract <;> simp only [combineSignedCounted, combineSigned, Bool.false_eq_true,
    ↓reduceIte, addSignedCounted_value, subtractSignedCounted_value]

theorem combineSignedCounted_steps_le {n : ℕ} (subtract : Bool) (start sx : ℕ)
    (xs : List ℕ) (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (combineSignedCounted (n := n) subtract start sx xs sy ys).steps ≤ 512 * (xs.length + 1) := by
  cases subtract <;>
    simp only [combineSignedCounted, Bool.false_eq_true, ↓reduceIte,
      addSignedCounted_steps _ _ _ _ _ hlen, subtractSignedCounted_steps _ _ _ _ _ hlen] <;> omega

def combineFractionsCounted {n : ℕ} (subtract : Bool) (start : ℕ) (x y : FractionRefs) :
    Execution (List (CGate n) × FractionRefs) :=
  let cross := crossProductsCounted start x y
  let cl := lengthFrom 0 cross.value.1
  let ns := addIndex start cl.value
  let num := combineSignedCounted subtract ns.value x.sign cross.value.2.left y.sign cross.value.2.right
  let nl := lengthFrom 0 num.value.1
  let zs := addIndex ns.value nl.value
  let den := appendList cross.value.2.denominator [start]
  let norm := normalizeWordsCounted zs.value num.value.2.2 den.value
  let first := appendList cross.value.1 num.value.1
  let code := appendList first.value norm.value.1
  ⟨(code.value, ⟨num.value.2.1, norm.value.2.1, norm.value.2.2⟩),
    cross.steps + cl.steps + ns.steps + num.steps + nl.steps + zs.steps + den.steps +
      norm.steps + first.steps + code.steps + 4⟩

theorem combineFractionsCounted_value {n : ℕ} (subtract : Bool) (start : ℕ) (x y : FractionRefs) :
    (combineFractionsCounted (n := n) subtract start x y).value =
      combineFractions subtract start x y := by
  simp only [combineFractionsCounted, crossProductsCounted_value, lengthFrom_value,
    Nat.zero_add, addIndex_value, combineSignedCounted_value, appendList_value,
    normalizeWordsCounted_value, combineFractions]

theorem combineFractionsCounted_steps_le {n : ℕ} (subtract : Bool) (start : ℕ)
    (x y : FractionRefs) (w : ℕ) (hx : Width x w) (hy : Width y w) :
    (combineFractionsCounted (n := n) subtract start x y).steps ≤ 3000000 * (w + 1) ^ 5 := by
  let cross := crossProducts (n := n) start x y
  let num := combineSigned (n := n) subtract (start + cross.1.length)
    x.sign cross.2.left y.sign cross.2.right
  have hl := crossProducts_lengths (n := n) start x y w hx hy
  change cross.2.left.length = _ ∧ cross.2.right.length = _ ∧ cross.2.denominator.length = _ at hl
  have hsame := hl.1.trans hl.2.1.symm
  have hn : num.2.2.length = 2 * w + 1 := by
    rw [combineSigned_word_length _ _ _ _ _ _ hsame, hl.1]
  have hden : (cross.2.denominator ++ [start]).length = 2 * w + 1 := by
    simp only [List.length_append, List.length_singleton, hl.2.2]
  have hc := crossProductsCounted_steps_le (n := n) start x y w hx hy
  have hnum := combineSignedCounted_steps_le (n := n) subtract (start + cross.1.length)
    x.sign cross.2.left y.sign cross.2.right hsame
  rw [hl.1] at hnum
  have hnorm := normalizeWordsCounted_steps_le (n := n)
    (start + cross.1.length + num.1.length) num.2.2 (cross.2.denominator ++ [start]) (hn.trans hden.symm)
  rw [hn] at hnorm
  have hnscale : 65536 * (2 * w + 1 + 1) ^ 5 = 2097152 * (w + 1) ^ 5 := by ring
  rw [hnscale] at hnorm
  have hcg := crossProducts_gate_count (n := n) start x y w hx hy
  change cross.1.length ≤ _ at hcg
  have hng := combineSigned_gate_count (n := n) subtract (start + cross.1.length)
    x.sign cross.2.left y.sign cross.2.right hsame
  change num.1.length ≤ _ at hng
  rw [hl.1] at hng
  have h45 : (w + 1) ^ 4 ≤ (w + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h35 : (w + 1) ^ 3 ≤ (w + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h15 : w + 1 ≤ (w + 1) ^ 5 := by
    calc
      _ = (w + 1) ^ 1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  simp only [combineFractionsCounted, crossProductsCounted_value, lengthFrom_steps,
    lengthFrom_value, Nat.zero_add, addIndex_steps, addIndex_value, combineSignedCounted_value,
    appendList_steps, appendList_value, List.length_append]
  change _ + (2 * cross.1.length + 1) + (cross.1.length + 1) + _ +
    (2 * num.1.length + 1) + (num.1.length + 1) + (cross.2.denominator.length + 1) + _ +
      (cross.1.length + 1) + (cross.1.length + num.1.length + 1) + 4 ≤ _
  rw [hl.2.2]
  dsimp only [cross, num] at *
  omega

def addFractionsCounted {n : ℕ} (start : ℕ) (x y : FractionRefs) :
    Execution (List (CGate n) × FractionRefs) := combineFractionsCounted false start x y

def subtractFractionsCounted {n : ℕ} (start : ℕ) (x y : FractionRefs) :
    Execution (List (CGate n) × FractionRefs) := combineFractionsCounted true start x y

theorem addFractionsCounted_value {n : ℕ} (start : ℕ) (x y : FractionRefs) :
    (addFractionsCounted (n := n) start x y).value = addFractions start x y :=
  combineFractionsCounted_value false start x y

theorem subtractFractionsCounted_value {n : ℕ} (start : ℕ) (x y : FractionRefs) :
    (subtractFractionsCounted (n := n) start x y).value = subtractFractions start x y :=
  combineFractionsCounted_value true start x y

theorem addFractionsCounted_steps_le {n : ℕ} (start : ℕ) (x y : FractionRefs)
    (w : ℕ) (hx : Width x w) (hy : Width y w) :
    (addFractionsCounted (n := n) start x y).steps ≤ 3000000 * (w + 1) ^ 5 :=
  combineFractionsCounted_steps_le false start x y w hx hy

theorem subtractFractionsCounted_steps_le {n : ℕ} (start : ℕ) (x y : FractionRefs)
    (w : ℕ) (hx : Width x w) (hy : Width y w) :
    (subtractFractionsCounted (n := n) start x y).steps ≤ 3000000 * (w + 1) ^ 5 :=
  combineFractionsCounted_steps_le true start x y w hx hy

theorem addFractionsCounted_width {n : ℕ} (start : ℕ) (x y : FractionRefs)
    (w : ℕ) (hx : Width x w) (hy : Width y w) :
    Width (addFractionsCounted (n := n) start x y).value.2 (2 * w + 1) := by
  rw [addFractionsCounted_value]
  exact addFractions_width start x y w hx hy

theorem subtractFractionsCounted_width {n : ℕ} (start : ℕ) (x y : FractionRefs)
    (w : ℕ) (hx : Width x w) (hy : Width y w) :
    Width (subtractFractionsCounted (n := n) start x y).value.2 (2 * w + 1) := by
  rw [subtractFractionsCounted_value]
  exact subtractFractions_width start x y w hx hy

theorem addFractionsCounted_valid {n : ℕ} (start : ℕ) (x y : FractionRefs)
    (w : ℕ) (hx : Width x w) (hy : Width y w) :
    Valid (addFractionsCounted (n := n) start x y).value.2
      (start + (addFractionsCounted (n := n) start x y).value.1.length) := by
  rw [addFractionsCounted_value]
  exact addFractions_valid start x y w hx hy

theorem subtractFractionsCounted_valid {n : ℕ} (start : ℕ) (x y : FractionRefs)
    (w : ℕ) (hx : Width x w) (hy : Width y w) :
    Valid (subtractFractionsCounted (n := n) start x y).value.2
      (start + (subtractFractionsCounted (n := n) start x y).value.1.length) := by
  rw [subtractFractionsCounted_value]
  exact subtractFractions_valid start x y w hx hy

theorem addFractionsCounted_represents {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (x y : FractionRefs) (q r : ℚ) (w : ℕ)
    (hxw : Width x w) (hyw : Width y w) (hxv : Valid x vals.length) (hyv : Valid y vals.length)
    (hx : Represents vals x q) (hy : Represents vals y r) :
    Represents (runFrom a vals (addFractionsCounted vals.length x y).value.1)
      (addFractionsCounted (n := n) vals.length x y).value.2 (q + r) := by
  rw [addFractionsCounted_value]
  exact addFractions_represents a vals x y q r w hxw hyw hxv hyv hx hy

theorem subtractFractionsCounted_represents {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (x y : FractionRefs) (q r : ℚ) (w : ℕ)
    (hxw : Width x w) (hyw : Width y w) (hxv : Valid x vals.length) (hyv : Valid y vals.length)
    (hx : Represents vals x q) (hy : Represents vals y r) :
    Represents (runFrom a vals (subtractFractionsCounted vals.length x y).value.1)
      (subtractFractionsCounted (n := n) vals.length x y).value.2 (q - r) := by
  rw [subtractFractionsCounted_value]
  exact subtractFractions_represents a vals x y q r w hxw hyw hxv hyv hx hy

end GodMoveRationalAddCompileCost

#print axioms GodMoveRationalAddCompileCost.crossProductsCounted_value
#print axioms GodMoveRationalAddCompileCost.crossProductsCounted_steps_le
#print axioms GodMoveRationalAddCompileCost.combineSignedCounted_value
#print axioms GodMoveRationalAddCompileCost.combineSignedCounted_steps_le
#print axioms GodMoveRationalAddCompileCost.combineFractionsCounted_value
#print axioms GodMoveRationalAddCompileCost.combineFractionsCounted_steps_le
#print axioms GodMoveRationalAddCompileCost.addFractionsCounted_value
#print axioms GodMoveRationalAddCompileCost.subtractFractionsCounted_value
#print axioms GodMoveRationalAddCompileCost.addFractionsCounted_steps_le
#print axioms GodMoveRationalAddCompileCost.subtractFractionsCounted_steps_le
#print axioms GodMoveRationalAddCompileCost.addFractionsCounted_width
#print axioms GodMoveRationalAddCompileCost.subtractFractionsCounted_width
#print axioms GodMoveRationalAddCompileCost.addFractionsCounted_valid
#print axioms GodMoveRationalAddCompileCost.subtractFractionsCounted_valid
#print axioms GodMoveRationalAddCompileCost.addFractionsCounted_represents
#print axioms GodMoveRationalAddCompileCost.subtractFractionsCounted_represents
