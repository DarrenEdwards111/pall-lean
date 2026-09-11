import GodMoveBinaryRationalMultiply

/-!
# Rational division with an emitted reciprocal zero guard

A reciprocal circuit tests the variable numerator, swaps numerator and
denominator at nonzero, and selects explicit zero/one words at zero. It retains
the original sign reference, allowing negative zero. Composing this circuit
with the canonical rational multiplier gives actual division, including the
totalized zero-divisor convention. Bounds count emitted Boolean gates only.
-/

namespace GodMoveBinaryRationalDivide

open GodMoveBinaryAdder GodMoveBinaryGCD GodMoveBinaryDivision
open GodMoveBinaryRationalMultiply GodMoveRationalWireEncoding
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- A width-exact one word; at zero width its value is zero. Canonical rational
input representations force positive width when this constant is needed. -/
def oneWord (start width : ℕ) : List ℕ :=
  ((start + 1) :: List.replicate width start).take width

theorem oneWord_length (start width : ℕ) : (oneWord start width).length = width := by
  simp [oneWord]

theorem oneWord_refs_lt (start width : ℕ) :
    ∀ i ∈ oneWord start width, i < start + 2 := by
  intro i hi
  have h := List.mem_of_mem_take hi
  rcases List.mem_cons.mp h with h | h
  · omega
  · have he := List.eq_of_mem_replicate h
    omega

theorem oneWord_value (vals : List Bool) (start width : ℕ) (hw : 0 < width)
    (hz : vals.getD start false = false) (ho : vals.getD (start + 1) false = true) :
    wordValue vals (oneWord start width) = 1 := by
  cases width with
  | zero => omega
  | succ w =>
    simp only [oneWord, List.take_succ_cons, wordValue, ho, Bool.toNat_true]
    have h : wordValue vals ((List.replicate (w + 1) start).take w) = 0 := by
      simpa only [List.take_replicate, Nat.min_eq_left (Nat.le_succ _)] using
        wordValue_replicate_zero vals start hz w
    rw [h]

def reciprocalFraction {n : ℕ} (start : ℕ) (x : FractionRefs) :
    List (CGate n) × FractionRefs :=
  let zeros := List.replicate x.numerator.length start
  let nz := nonzeroWord (start + 2) x.numerator
  let num := chooseWords (start + 2 + nz.1.length) nz.2 x.denominator zeros
  let den := chooseWords (start + 2 + nz.1.length + num.1.length) nz.2
    x.numerator (oneWord start x.numerator.length)
  ((([.cst false, .cst true] ++ nz.1) ++ num.1) ++ den.1,
    ⟨x.sign, num.2, den.2⟩)

theorem reciprocalFraction_width {n : ℕ} (start : ℕ) (x : FractionRefs) (w : ℕ)
    (hx : Width x w) : Width (reciprocalFraction (n := n) start x).2 w := by
  have hn : x.denominator.length = (List.replicate x.numerator.length start).length := by
    simp only [List.length_replicate, hx.1, hx.2]
  have hd : x.numerator.length = (oneWord start x.numerator.length).length :=
    (oneWord_length _ _).symm
  constructor
  · exact (chooseWords_word_length _ _ _ _ hn).trans hx.2
  · exact (chooseWords_word_length _ _ _ _ hd).trans hx.1

theorem reciprocalFraction_gate_count {n : ℕ} (start : ℕ) (x : FractionRefs) (w : ℕ)
    (hx : Width x w) :
    (reciprocalFraction (n := n) start x).1.length = 8 * w + 4 := by
  let nz := nonzeroWord (n := n) (start + 2) x.numerator
  let num := chooseWords (n := n) (start + 2 + nz.1.length) nz.2 x.denominator
    (List.replicate x.numerator.length start)
  let den := chooseWords (n := n) (start + 2 + nz.1.length + num.1.length) nz.2
    x.numerator (oneWord start x.numerator.length)
  have hnlen : x.denominator.length = (List.replicate x.numerator.length start).length := by
    simp only [List.length_replicate, hx.1, hx.2]
  have hdlen : x.numerator.length = (oneWord start x.numerator.length).length :=
    (oneWord_length _ _).symm
  have hn : num.1.length = 3 * w :=
    (chooseWords_gate_count _ _ _ _ hnlen).trans (congrArg (3 * ·) hx.2)
  have hd : den.1.length = 3 * w :=
    (chooseWords_gate_count _ _ _ _ hdlen).trans (congrArg (3 * ·) hx.1)
  have hz : nz.1.length = 2 * w + 2 := by
    simp only [nz, nonzeroWord_gate_count, hx.1]
  change ((([CGate.cst false, CGate.cst true] ++ nz.1) ++ num.1) ++ den.1).length = _
  simp only [List.length_append, List.length_cons, List.length_nil, hn, hd, hz]
  omega

theorem reciprocalFraction_valid {n : ℕ} (start : ℕ) (x : FractionRefs)
    (hx : Valid x start) :
    Valid (reciprocalFraction (n := n) start x).2
      (start + (reciprocalFraction (n := n) start x).1.length) := by
  let nz := nonzeroWord (n := n) (start + 2) x.numerator
  let num := chooseWords (n := n) (start + 2 + nz.1.length) nz.2 x.denominator
    (List.replicate x.numerator.length start)
  let den := chooseWords (n := n) (start + 2 + nz.1.length + num.1.length) nz.2
    x.numerator (oneWord start x.numerator.length)
  have hn := chooseWords_refs_lt (n := n) (start + 2 + nz.1.length) nz.2
    x.denominator (List.replicate x.numerator.length start)
  have hd := chooseWords_refs_lt (n := n) (start + 2 + nz.1.length + num.1.length) nz.2
    x.numerator (oneWord start x.numerator.length)
  change x.sign < start + ((([CGate.cst false, CGate.cst true] ++ nz.1) ++ num.1) ++ den.1).length ∧
    (∀ i ∈ num.2, i < start + ((([CGate.cst false, CGate.cst true] ++ nz.1) ++ num.1) ++ den.1).length) ∧
    (∀ i ∈ den.2, i < start + ((([CGate.cst false, CGate.cst true] ++ nz.1) ++ num.1) ++ den.1).length)
  simp only [List.length_append, List.length_cons, List.length_nil]
  constructor
  · have h := hx.1; omega
  · constructor
    · intro i hi
      have h := hn i hi
      change i < start + 2 + nz.1.length + num.1.length at h
      omega
    · intro i hi
      have h := hd i hi
      change i < start + 2 + nz.1.length + num.1.length + den.1.length at h
      omega

private theorem reciprocal_components (b : Bool) (N D : ℕ) (q : ℚ)
    (hn : signedMagnitude b N = q.num) (hd : D = q.den) :
    signedMagnitude b (if N = 0 then 0 else D) = (q⁻¹).num ∧
      (if N = 0 then 1 else N) = (q⁻¹).den := by
  rw [Rat.num_inv, Rat.den_inv, ← hn, ← hd]
  by_cases hN : N = 0
  · subst N
    cases b <;> simp [signedMagnitude]
  · have hp : 0 < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hnz : (N : ℤ) ≠ 0 := ne_of_gt hp
    cases b with
    | false =>
      simp only [signedMagnitude, Bool.false_eq_true, ↓reduceIte, Int.natAbs_natCast,
        if_neg hN, if_neg hnz, Int.sign_eq_one_of_pos hp, one_mul, and_self]
    | true =>
      simp only [signedMagnitude, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast,
        if_neg hN, if_neg (neg_ne_zero.mpr hnz),
        Int.sign_eq_neg_one_of_neg (neg_neg_of_pos hp), neg_one_mul, and_self]

theorem reciprocalFraction_represents {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (x : FractionRefs) (q : ℚ) (w : ℕ) (hxw : Width x w)
    (hxv : Valid x vals.length) (hx : Represents vals x q) :
    Represents (runFrom a vals (reciprocalFraction vals.length x).1)
      (reciprocalFraction (n := n) vals.length x).2 q⁻¹ := by
  have hw : 0 < x.numerator.length := by
    have hp := hx.denominator_pos
    by_contra h
    have hn : x.numerator.length = 0 := by omega
    have hd : x.denominator = [] := List.eq_nil_of_length_eq_zero (by rw [hxw.2, ← hxw.1, hn])
    simp only [hd, wordValue] at hp
    omega
  let constants : List (CGate n) := [.cst false, .cst true]
  let v0 := runFrom a vals constants
  have hl0 : v0.length = vals.length + 2 := by
    simp only [v0, runFrom_length, constants, List.length_cons, List.length_nil]
  have hz0 : v0.getD vals.length false = false := by
    simp only [v0, constants, runFrom, evalGate, List.append_assoc, List.singleton_append,
      read_append_start, List.getD_cons_zero]
  have ho0 : v0.getD (vals.length + 1) false = true := by
    change ((vals ++ [false]) ++ [true]).getD (vals.length + 1) false = true
    have h : (vals ++ [false]).length = vals.length + 1 := by simp
    rw [← h, read_append_start]
    rfl
  have hxv0 : Valid x v0.length := hxv.mono (by rw [hl0]; omega)
  let nz := nonzeroWord (n := n) v0.length x.numerator
  let v1 := runFrom a v0 nz.1
  have hl1 : v1.length = v0.length + nz.1.length := runFrom_length _ _ _
  have hxv1 : Valid x v1.length := hxv0.mono (by rw [hl1]; omega)
  let zeros := List.replicate x.numerator.length vals.length
  let num := chooseWords (n := n) v1.length nz.2 x.denominator zeros
  let v2 := runFrom a v1 num.1
  have hl2 : v2.length = v1.length + num.1.length := runFrom_length _ _ _
  have hxv2 : Valid x v2.length := hxv1.mono (by rw [hl2]; omega)
  let den := chooseWords (n := n) v2.length nz.2 x.numerator
    (oneWord vals.length x.numerator.length)
  let v3 := runFrom a v2 den.1
  have hsnz1 : nz.2 < v1.length := by rw [hl1]; exact nonzeroWord_ref_lt _ _
  have hsnz2 : nz.2 < v2.length := by rw [hl2]; omega
  have hzv0 : vals.length < v0.length := by rw [hl0]; omega
  have hov0 : vals.length + 1 < v0.length := by rw [hl0]; omega
  have hzv1 : vals.length < v1.length := by rw [hl1]; omega
  have hov1 : vals.length + 1 < v1.length := by rw [hl1]; omega
  have hz1 : v1.getD vals.length false = false :=
    (read_runFrom_old a v0 nz.1 vals.length hzv0).trans hz0
  have hz2 : v2.getD vals.length false = false :=
    (read_runFrom_old a v1 num.1 vals.length hzv1).trans hz1
  have ho2 : v2.getD (vals.length + 1) false = true :=
    (read_runFrom_old a v1 num.1 (vals.length + 1) hov1).trans
      ((read_runFrom_old a v0 nz.1 (vals.length + 1) hov0).trans ho0)
  have hzrefs : ∀ i ∈ zeros, i < v1.length := by
    intro i hi
    have h : i = vals.length := List.eq_of_mem_replicate hi
    omega
  have horefs : ∀ i ∈ oneWord vals.length x.numerator.length, i < v2.length := by
    intro i hi
    have h := oneWord_refs_lt vals.length x.numerator.length i hi
    rw [hl2, hl1, hl0]
    omega
  have hnlen : x.denominator.length = zeros.length := by
    simp only [zeros, List.length_replicate, hxw.1, hxw.2]
  have hdlen : x.numerator.length = (oneWord vals.length x.numerator.length).length :=
    (oneWord_length _ _).symm
  have hnum := chooseWords_spec a v1 nz.2 x.denominator zeros hnlen hsnz1 hxv1.2.2 hzrefs
  have hden := chooseWords_spec a v2 nz.2 x.numerator
    (oneWord vals.length x.numerator.length) hdlen hsnz2 hxv2.2.1 horefs
  have hnz : v1.getD nz.2 false = decide (wordValue vals x.numerator ≠ 0) := by
    have h := nonzeroWord_spec a v0 x.numerator hxv0.2.1
    rw [wordValue_runFrom_old a vals constants x.numerator hxv.2.1] at h
    exact h
  have hnz2 : v2.getD nz.2 false = decide (wordValue vals x.numerator ≠ 0) :=
    (read_runFrom_old a v1 num.1 nz.2 hsnz1).trans hnz
  have hD1 : wordValue v1 x.denominator = wordValue vals x.denominator :=
    (wordValue_runFrom_old a v0 nz.1 x.denominator hxv0.2.2).trans
      (wordValue_runFrom_old a vals constants x.denominator hxv.2.2)
  have hN2 : wordValue v2 x.numerator = wordValue vals x.numerator :=
    (wordValue_runFrom_old a v1 num.1 x.numerator hxv1.2.1).trans
      ((wordValue_runFrom_old a v0 nz.1 x.numerator hxv0.2.1).trans
        (wordValue_runFrom_old a vals constants x.numerator hxv.2.1))
  have hzvalue : wordValue v1 zeros = 0 := wordValue_replicate_zero v1 vals.length hz1 _
  have hovalue : wordValue v2 (oneWord vals.length x.numerator.length) = 1 :=
    oneWord_value v2 vals.length x.numerator.length hw hz2 ho2
  rw [hnz, hD1, hzvalue] at hnum
  rw [hnz2, hN2, hovalue] at hden
  have hnumrefs : ∀ i ∈ num.2, i < v2.length := by
    rw [hl2]; exact chooseWords_refs_lt _ _ _ _
  have hnumfinal : wordValue v3 num.2 =
      if wordValue vals x.numerator = 0 then 0 else wordValue vals x.denominator := by
    rw [wordValue_runFrom_old a v2 den.1 num.2 hnumrefs]
    simpa only [decide_eq_true_eq, ite_not] using hnum
  have hdenfinal : wordValue v3 den.2 =
      if wordValue vals x.numerator = 0 then 1 else wordValue vals x.numerator := by
    simpa only [decide_eq_true_eq, ite_not] using hden
  have hsignfinal : v3.getD x.sign false = vals.getD x.sign false :=
    (read_runFrom_old a v2 den.1 x.sign hxv2.1).trans
      ((read_runFrom_old a v1 num.1 x.sign hxv1.1).trans
        ((read_runFrom_old a v0 nz.1 x.sign hxv0.1).trans
          (read_runFrom_old a vals constants x.sign hxv.1)))
  have hc := reciprocal_components (vals.getD x.sign false)
    (wordValue vals x.numerator) (wordValue vals x.denominator) q hx.1 hx.2
  have hout : Represents v3 ⟨x.sign, num.2, den.2⟩ q⁻¹ := by
    constructor
    · change signedMagnitude (v3.getD x.sign false) (wordValue v3 num.2) = _
      rw [hsignfinal, hnumfinal]
      exact hc.1
    · exact hdenfinal.trans hc.2
  simpa only [reciprocalFraction, zeros, nz, num, den, v0, v1, v2, v3, constants,
    runFrom_append, runFrom_length, List.length_cons, List.length_nil] using hout

/-- Reciprocal output wires feed the existing rational multiplication circuit. -/
def divideFractions {n : ℕ} (start : ℕ) (x y : FractionRefs) :
    List (CGate n) × FractionRefs :=
  let inv := reciprocalFraction start y
  let product := multiplyFractions (start + inv.1.length) x inv.2
  (inv.1 ++ product.1, product.2)

theorem divideFractions_width {n : ℕ} (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    Width (divideFractions (n := n) start x y).2 (2 * w) :=
  multiplyFractions_width _ _ _ w hx (reciprocalFraction_width start y w hy)

theorem divideFractions_gate_count {n : ℕ} (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    (divideFractions (n := n) start x y).1.length ≤ 1040 * (w + 1) ^ 3 := by
  have hi := reciprocalFraction_gate_count (n := n) start y w hy
  have hp := multiplyFractions_gate_count (n := n)
    (start + (reciprocalFraction (n := n) start y).1.length)
    x (reciprocalFraction (n := n) start y).2 w hx (reciprocalFraction_width start y w hy)
  have hw : w + 1 ≤ (w + 1) ^ 3 := by
    calc w + 1 = (w + 1) ^ 1 := by simp
         _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  simp only [divideFractions, List.length_append]
  omega

theorem divideFractions_valid {n : ℕ} (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    Valid (divideFractions (n := n) start x y).2
      (start + (divideFractions (n := n) start x y).1.length) := by
  have h := multiplyFractions_valid (n := n)
    (start + (reciprocalFraction (n := n) start y).1.length)
    x (reciprocalFraction (n := n) start y).2 w hx (reciprocalFraction_width start y w hy)
  simpa only [divideFractions, List.length_append, Nat.add_assoc] using h

theorem divideFractions_represents {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (x y : FractionRefs) (q r : ℚ) (w : ℕ)
    (hxw : Width x w) (hyw : Width y w)
    (hxv : Valid x vals.length) (hyv : Valid y vals.length)
    (hx : Represents vals x q) (hy : Represents vals y r) :
    Represents (runFrom a vals (divideFractions vals.length x y).1)
      (divideFractions (n := n) vals.length x y).2 (q / r) := by
  let inv := reciprocalFraction (n := n) vals.length y
  let next := runFrom a vals inv.1
  have hlen : next.length = vals.length + inv.1.length := runFrom_length _ _ _
  have hi := reciprocalFraction_represents a vals y r w hyw hyv hy
  have hiv : Valid inv.2 next.length := by
    rw [hlen]
    exact reciprocalFraction_valid _ _ hyv
  have hxv' : Valid x next.length := hxv.mono (by rw [hlen]; omega)
  have h := multiplyFractions_represents a next x inv.2 q r⁻¹ w hxw
    (reciprocalFraction_width _ _ _ hyw) hxv' hiv (hx.runFrom_old a inv.1 hxv) hi
  simpa only [divideFractions, inv, next, runFrom_append, runFrom_length, div_eq_mul_inv] using h

theorem divideFractions_value {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (x y : FractionRefs) (q r : ℚ) (w : ℕ)
    (hxw : Width x w) (hyw : Width y w)
    (hxv : Valid x vals.length) (hyv : Valid y vals.length)
    (hx : Represents vals x q) (hy : Represents vals y r) :
    (divideFractions (n := n) vals.length x y).2.value
      (runFrom a vals (divideFractions vals.length x y).1) = q / r :=
  (divideFractions_represents a vals x y q r w hxw hyw hxv hyv hx hy).value_eq

private def reciprocalTwo (vals : List Bool) : Bool × (ℕ × ℕ) :=
  let code := reciprocalFraction (n := 0) vals.length ⟨0, [1, 2], [3, 4]⟩
  let out := runFrom (fun i => Fin.elim0 i) vals code.1
  (out.getD code.2.sign false,
    wordValue out code.2.numerator, wordValue out code.2.denominator)

/-- Negative zero is retained as a sign bit but canonically represents zero. -/
example : reciprocalTwo [true, false, false, true, false] = (true, 0, 1) := by decide

example : reciprocalTwo [true, false, true, true, true] = (true, 3, 2) := by decide

end GodMoveBinaryRationalDivide

#print axioms GodMoveBinaryRationalDivide.oneWord_value
#print axioms GodMoveBinaryRationalDivide.reciprocalFraction_width
#print axioms GodMoveBinaryRationalDivide.reciprocalFraction_gate_count
#print axioms GodMoveBinaryRationalDivide.reciprocalFraction_valid
#print axioms GodMoveBinaryRationalDivide.reciprocalFraction_represents
#print axioms GodMoveBinaryRationalDivide.divideFractions_width
#print axioms GodMoveBinaryRationalDivide.divideFractions_gate_count
#print axioms GodMoveBinaryRationalDivide.divideFractions_valid
#print axioms GodMoveBinaryRationalDivide.divideFractions_represents
#print axioms GodMoveBinaryRationalDivide.divideFractions_value
