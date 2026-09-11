import GodMoveRationalWireEncoding
import GodMoveBinaryMultiply

/-!
# Rational multiplication through emitted binary circuits

Two variable signed rational operands are multiplied using magnitude and
denominator product circuits, one xor sign gate, and the shared binary
normalizer. All numerical output bits are computed by emitted Boolean gates.
The gate count excludes code generation and host execution costs.
-/

namespace GodMoveBinaryRationalMultiply

open GodMoveBinaryAdder GodMoveBinaryMultiply GodMoveBinaryFractionNormalize
open GodMoveRationalWireEncoding GodMoveRationalPrimitiveBounds
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- The false and sign wires are ordinary emitted gates; numerator and
denominator product words are each materialized once before normalization. -/
def multiplyFractions {n : ℕ} (start : ℕ) (x y : FractionRefs) :
    List (CGate n) × FractionRefs :=
  let pn := productBits (start + 1) start x.numerator y.numerator
  let pd := productBits (start + 1 + pn.1.length) start x.denominator y.denominator
  let sign := start + 1 + pn.1.length + pd.1.length
  let norm := normalizeWords (sign + 1) pn.2 pd.2
  ((([.cst false] ++ pn.1) ++ pd.1) ++ ([.bin Bool.xor x.sign y.sign] ++ norm.1),
    ⟨sign, norm.2.1, norm.2.2⟩)

theorem multiplyFractions_width {n : ℕ} (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    Width (multiplyFractions (n := n) start x y).2 (2 * w) := by
  let pn := productBits (n := n) (start + 1) start x.numerator y.numerator
  let pd := productBits (n := n) (start + 1 + pn.1.length) start x.denominator y.denominator
  have hnlen : pn.2.length = 2 * w := by
    simp only [pn, productBits_word_length, hx.1, hy.1, two_mul]
  have hdlen : pd.2.length = 2 * w := by
    simp only [pd, productBits_word_length, hx.2, hy.2, two_mul]
  have h := normalizeWords_lengths (n := n)
    (start + 1 + pn.1.length + pd.1.length + 1) pn.2 pd.2 (hnlen.trans hdlen.symm)
  exact ⟨h.1.trans hnlen, h.2.trans hnlen⟩

theorem multiplyFractions_gate_count {n : ℕ} (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    (multiplyFractions (n := n) start x y).1.length ≤ 1024 * (w + 1) ^ 3 := by
  let pn := productBits (n := n) (start + 1) start x.numerator y.numerator
  let pd := productBits (n := n) (start + 1 + pn.1.length) start x.denominator y.denominator
  let sign := start + 1 + pn.1.length + pd.1.length
  let norm := normalizeWords (n := n) (sign + 1) pn.2 pd.2
  have hnlen : pn.2.length = 2 * w := by
    simp only [pn, productBits_word_length, hx.1, hy.1, two_mul]
  have hdlen : pd.2.length = 2 * w := by
    simp only [pd, productBits_word_length, hx.2, hy.2, two_mul]
  have hn := productBits_gate_count_le (n := n) (start + 1) start x.numerator y.numerator
  have hd := productBits_gate_count_le (n := n) (start + 1 + pn.1.length)
    start x.denominator y.denominator
  have hm := normalizeWords_gate_count (n := n) (sign + 1) pn.2 pd.2
    (hnlen.trans hdlen.symm)
  change pn.1.length ≤ _ at hn
  change pd.1.length ≤ _ at hd
  change norm.1.length ≤ _ at hm
  rw [hx.1, hy.1] at hn
  rw [hx.2, hy.2] at hd
  rw [hnlen] at hm
  have h2 : (2 * w + 1) ^ 3 ≤ 8 * (w + 1) ^ 3 := by
    calc
      _ ≤ (2 * (w + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) _
      _ = _ := by ring
  have hp : w * (w + 1) * (w + 2) ≤ 2 * (w + 1) ^ 3 := by
    calc
      _ ≤ (w + 1) * (w + 1) * (2 * (w + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (by omega)
      _ = _ := by ring
  have hpos : 1 ≤ (w + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  change ((([CGate.cst false] ++ pn.1) ++ pd.1) ++
    ([CGate.bin Bool.xor x.sign y.sign] ++ norm.1)).length ≤ _
  simp only [List.length_append, List.length_singleton]
  nlinarith

theorem multiplyFractions_valid {n : ℕ} (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hxw : Width x w) (hyw : Width y w) :
    Valid (multiplyFractions (n := n) start x y).2
      (start + (multiplyFractions (n := n) start x y).1.length) := by
  let pn := productBits (n := n) (start + 1) start x.numerator y.numerator
  let pd := productBits (n := n) (start + 1 + pn.1.length) start x.denominator y.denominator
  let sign := start + 1 + pn.1.length + pd.1.length
  let norm := normalizeWords (n := n) (sign + 1) pn.2 pd.2
  have hnlen : pn.2.length = 2 * w := by
    simp only [pn, productBits_word_length, hxw.1, hyw.1, two_mul]
  have hdlen : pd.2.length = 2 * w := by
    simp only [pd, productBits_word_length, hxw.2, hyw.2, two_mul]
  have hn : ∀ i ∈ pn.2, i < sign + 1 := by
    intro i hi
    have h := productBits_refs_lt (n := n) (start + 1) start x.numerator y.numerator
      (by omega) i hi
    change i < start + 1 + pn.1.length at h
    dsimp [sign]
    omega
  have hd : ∀ i ∈ pd.2, i < sign + 1 := by
    intro i hi
    have h := productBits_refs_lt (n := n) (start + 1 + pn.1.length) start
      x.denominator y.denominator (by omega) i hi
    change i < start + 1 + pn.1.length + pd.1.length at h
    dsimp [sign]
    omega
  have hm := normalizeWords_refs_lt (n := n) (sign + 1) pn.2 pd.2
    (hnlen.trans hdlen.symm) hn hd
  change sign < start + ((([CGate.cst false] ++ pn.1) ++ pd.1) ++
    ([CGate.bin Bool.xor x.sign y.sign] ++ norm.1)).length ∧
    (∀ i ∈ norm.2.1, i < start + ((([CGate.cst false] ++ pn.1) ++ pd.1) ++
      ([CGate.bin Bool.xor x.sign y.sign] ++ norm.1)).length) ∧
    (∀ i ∈ norm.2.2, i < start + ((([CGate.cst false] ++ pn.1) ++ pd.1) ++
      ([CGate.bin Bool.xor x.sign y.sign] ++ norm.1)).length)
  simp only [List.length_append, List.length_singleton]
  constructor
  · dsimp [sign]; omega
  · constructor
    · intro i hi
      have h := hm.1 i hi
      change i < sign + 1 + norm.1.length at h
      dsimp [sign] at h
      omega
    · intro i hi
      have h := hm.2 i hi
      change i < sign + 1 + norm.1.length at h
      dsimp [sign] at h
      omega

/-- The represented operands may share references. The product is represented
by its canonical components, with either encoding of zero's sign accepted. -/
theorem multiplyFractions_represents {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (x y : FractionRefs) (q r : ℚ) (w : ℕ)
    (hxw : Width x w) (hyw : Width y w)
    (hxv : Valid x vals.length) (hyv : Valid y vals.length)
    (hx : Represents vals x q) (hy : Represents vals y r) :
    Represents (runFrom a vals (multiplyFractions vals.length x y).1)
      (multiplyFractions (n := n) vals.length x y).2 (q * r) := by
  let v0 := runFrom a vals [CGate.cst false]
  have hl0 : v0.length = vals.length + 1 := by simp only [v0, runFrom_length, List.length_singleton]
  have hz0 : vals.length < v0.length := by rw [hl0]; omega
  have hzval0 : v0.getD vals.length false = false := by
    simp only [v0, runFrom, evalGate, read_append_start, List.getD_cons_zero]
  have hxv0 : Valid x v0.length := hxv.mono (by rw [hl0]; omega)
  have hyv0 : Valid y v0.length := hyv.mono (by rw [hl0]; omega)
  let pn := productBits (n := n) v0.length vals.length x.numerator y.numerator
  let v1 := runFrom a v0 pn.1
  have hl1 : v1.length = v0.length + pn.1.length := runFrom_length _ _ _
  have hxv1 : Valid x v1.length := hxv0.mono (by rw [hl1]; omega)
  have hyv1 : Valid y v1.length := hyv0.mono (by rw [hl1]; omega)
  have hz1 : vals.length < v1.length := by rw [hl1]; omega
  have hzval1 : v1.getD vals.length false = false :=
    (read_runFrom_old a v0 pn.1 vals.length hz0).trans hzval0
  let pd := productBits (n := n) v1.length vals.length x.denominator y.denominator
  let v2 := runFrom a v1 pd.1
  have hl2 : v2.length = v1.length + pd.1.length := runFrom_length _ _ _
  have hxv2 : Valid x v2.length := hxv1.mono (by rw [hl2]; omega)
  have hyv2 : Valid y v2.length := hyv1.mono (by rw [hl2]; omega)
  let signCode : List (CGate n) := [.bin Bool.xor x.sign y.sign]
  let v3 := runFrom a v2 signCode
  have hl3 : v3.length = v2.length + 1 := by simp only [v3, runFrom_length, signCode, List.length_singleton]
  let raw : FractionRefs := ⟨v2.length, pn.2, pd.2⟩
  have hpn1 : ∀ i ∈ pn.2, i < v1.length := by
    rw [hl1]
    exact productBits_refs_lt _ _ _ _ hz0
  have hpn2 : ∀ i ∈ pn.2, i < v2.length := by
    intro i hi; have h := hpn1 i hi; rw [hl2]; omega
  have hpn3 : ∀ i ∈ pn.2, i < v3.length := by
    intro i hi; have h := hpn2 i hi; rw [hl3]; omega
  have hpd2 : ∀ i ∈ pd.2, i < v2.length := by
    rw [hl2]
    exact productBits_refs_lt _ _ _ _ hz1
  have hpd3 : ∀ i ∈ pd.2, i < v3.length := by
    intro i hi; have h := hpd2 i hi; rw [hl3]; omega
  have hrawvalid : Valid raw v3.length := ⟨by dsimp [raw]; rw [hl3]; omega, hpn3, hpd3⟩
  have hlen : raw.numerator.length = raw.denominator.length := by
    simp only [raw, pn, pd, productBits_word_length, hxw.1, hxw.2, hyw.1, hyw.2]
  have hpnval := productBits_spec a v0 vals.length x.numerator y.numerator
    hz0 hzval0 hxv0.2.1 hyv0.2.1
  have hpdval := productBits_spec a v1 vals.length x.denominator y.denominator
    hz1 hzval1 hxv1.2.2 hyv1.2.2
  have hx0 := hx.runFrom_old a [CGate.cst false] hxv
  have hy0 := hy.runFrom_old a [CGate.cst false] hyv
  have hx1 := hx0.runFrom_old a pn.1 hxv0
  have hy1 := hy0.runFrom_old a pn.1 hyv0
  have hnumval : wordValue v3 pn.2 = wordValue vals x.numerator * wordValue vals y.numerator := by
    rw [wordValue_runFrom_old a v2 signCode pn.2 hpn2,
      wordValue_runFrom_old a v1 pd.1 pn.2 hpn1]
    change wordValue v1 pn.2 = _ at hpnval
    rw [wordValue_runFrom_old a vals [CGate.cst false] x.numerator hxv.2.1,
      wordValue_runFrom_old a vals [CGate.cst false] y.numerator hyv.2.1] at hpnval
    exact hpnval
  have hdenval : wordValue v3 pd.2 = q.den * r.den := by
    rw [wordValue_runFrom_old a v2 signCode pd.2 hpd2]
    change wordValue v2 pd.2 = _ at hpdval
    rw [hx1.2, hy1.2] at hpdval
    exact hpdval
  have hsx : v2.getD x.sign false = vals.getD x.sign false :=
    (read_runFrom_old a v1 pd.1 x.sign hxv1.1).trans
      ((read_runFrom_old a v0 pn.1 x.sign hxv0.1).trans
        (read_runFrom_old a vals [CGate.cst false] x.sign hxv.1))
  have hsy : v2.getD y.sign false = vals.getD y.sign false :=
    (read_runFrom_old a v1 pd.1 y.sign hyv1.1).trans
      ((read_runFrom_old a v0 pn.1 y.sign hyv0.1).trans
        (read_runFrom_old a vals [CGate.cst false] y.sign hyv.1))
  have hsign : v3.getD raw.sign false =
      Bool.xor (vals.getD x.sign false) (vals.getD y.sign false) := by
    simp only [v3, raw, signCode, runFrom, evalGate, read_append_start, List.getD_cons_zero,
      hsx, hsy]
  have hrawnum : signedValue v3 raw.sign raw.numerator = (rawMul q r).numerator := by
    change signedMagnitude (v3.getD raw.sign false) (wordValue v3 pn.2) = q.num * r.num
    rw [hsign, hnumval, signedMagnitude_mul]
    exact congrArg₂ (· * ·) hx.1 hy.1
  have hrawden : wordValue v3 raw.denominator = (rawMul q r).denominator := hdenval
  have hnorm := normalizeWords_represents a v3 raw hlen hrawvalid (rawMul q r) hrawnum hrawden
  rw [normalize_rawMul] at hnorm
  simpa only [multiplyFractions, raw, pn, pd, v0, v1, v2, v3, signCode,
    runFrom_append, runFrom_length, List.length_singleton] using hnorm

/-- Decoded equality follows from the stronger canonical component theorem. -/
theorem multiplyFractions_value {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (x y : FractionRefs) (q r : ℚ) (w : ℕ)
    (hxw : Width x w) (hyw : Width y w)
    (hxv : Valid x vals.length) (hyv : Valid y vals.length)
    (hx : Represents vals x q) (hy : Represents vals y r) :
    (multiplyFractions (n := n) vals.length x y).2.value
      (runFrom a vals (multiplyFractions vals.length x y).1) = q * r :=
  (multiplyFractions_represents a vals x y q r w hxw hyw hxv hyv hx hy).value_eq

end GodMoveBinaryRationalMultiply

#print axioms GodMoveBinaryRationalMultiply.multiplyFractions_width
#print axioms GodMoveBinaryRationalMultiply.multiplyFractions_gate_count
#print axioms GodMoveBinaryRationalMultiply.multiplyFractions_valid
#print axioms GodMoveBinaryRationalMultiply.multiplyFractions_represents
#print axioms GodMoveBinaryRationalMultiply.multiplyFractions_value
