import GodMoveSignedArithmetic
import GodMoveBinaryMultiply

/-!
# Canonical rational addition and subtraction by Boolean circuits

The emitted backend computes both signed cross products and the denominator
product, combines the signed numerators, and runs the verified binary
normalizer. The cost is an emitted gate bound; generating and executing the
whole rational-construction pipeline are separate obligations.
-/

namespace GodMoveBinaryRationalAdd

open GodMoveBinaryAdder GodMoveBinaryMultiply GodMoveBinaryDivision
open GodMoveBinaryFractionNormalize GodMoveSignedArithmetic
open GodMoveRationalWireEncoding GodMoveRationalPrimitiveBounds
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

structure CrossRefs where
  left : List ℕ
  right : List ℕ
  denominator : List ℕ
  deriving Repr, DecidableEq

def crossProducts {n : ℕ} (start : ℕ) (x y : FractionRefs) : List (CGate n) × CrossRefs :=
  let l := productBits (start + 1) start x.numerator y.denominator
  let r := productBits (start + 1 + l.1.length) start y.numerator x.denominator
  let d := productBits (start + 1 + l.1.length + r.1.length) start x.denominator y.denominator
  ([.cst false] ++ l.1 ++ r.1 ++ d.1, ⟨l.2, r.2, d.2⟩)

theorem crossProducts_lengths {n : ℕ} (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    (crossProducts (n := n) start x y).2.left.length = 2 * w ∧
      (crossProducts (n := n) start x y).2.right.length = 2 * w ∧
      (crossProducts (n := n) start x y).2.denominator.length = 2 * w := by
  simp only [crossProducts, productBits_word_length, hx.1, hx.2, hy.1, hy.2, two_mul,
    and_self]

theorem crossProducts_gate_count {n : ℕ} (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    (crossProducts (n := n) start x y).1.length ≤ 37 * (w + 1) ^ 3 := by
  let l := productBits (n := n) (start + 1) start x.numerator y.denominator
  let r := productBits (n := n) (start + 1 + l.1.length) start y.numerator x.denominator
  let d := productBits (n := n) (start + 1 + l.1.length + r.1.length) start x.denominator y.denominator
  have hl := productBits_gate_count_le (n := n) (start + 1) start x.numerator y.denominator
  have hr := productBits_gate_count_le (n := n) (start + 1 + l.1.length) start y.numerator x.denominator
  have hd := productBits_gate_count_le (n := n) (start + 1 + l.1.length + r.1.length) start x.denominator y.denominator
  change l.1.length ≤ _ at hl
  change r.1.length ≤ _ at hr
  change d.1.length ≤ _ at hd
  rw [hx.1, hy.2] at hl
  rw [hy.1, hx.2] at hr
  rw [hx.2, hy.2] at hd
  have hp : w * (w + 1) * (w + 2) ≤ 2 * (w + 1) ^ 3 := by
    calc
      _ ≤ (w + 1) * (w + 1) * (2 * (w + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (by omega)
      _ = _ := by ring
  have hpos : 1 ≤ (w + 1) ^ 3 := Nat.one_le_pow 3 (w + 1) (by omega)
  change ([CGate.cst false] ++ l.1 ++ r.1 ++ d.1).length ≤ _
  simp only [List.length_append, List.length_singleton]
  nlinarith

theorem crossProducts_refs_lt {n : ℕ} (start : ℕ) (x y : FractionRefs) :
    start < start + (crossProducts (n := n) start x y).1.length ∧
      (∀ i ∈ (crossProducts (n := n) start x y).2.left,
        i < start + (crossProducts (n := n) start x y).1.length) ∧
      (∀ i ∈ (crossProducts (n := n) start x y).2.right,
        i < start + (crossProducts (n := n) start x y).1.length) ∧
      (∀ i ∈ (crossProducts (n := n) start x y).2.denominator,
        i < start + (crossProducts (n := n) start x y).1.length) := by
  let l := productBits (n := n) (start + 1) start x.numerator y.denominator
  let r := productBits (n := n) (start + 1 + l.1.length) start y.numerator x.denominator
  let d := productBits (n := n) (start + 1 + l.1.length + r.1.length) start x.denominator y.denominator
  have hl := productBits_refs_lt (n := n) (start + 1) start x.numerator y.denominator (by omega)
  have hr := productBits_refs_lt (n := n) (start + 1 + l.1.length) start y.numerator x.denominator (by omega)
  have hd := productBits_refs_lt (n := n) (start + 1 + l.1.length + r.1.length) start x.denominator y.denominator (by omega)
  change start < start + ([CGate.cst false] ++ l.1 ++ r.1 ++ d.1).length ∧
    (∀ i ∈ l.2, i < start + ([CGate.cst false] ++ l.1 ++ r.1 ++ d.1).length) ∧
    (∀ i ∈ r.2, i < start + ([CGate.cst false] ++ l.1 ++ r.1 ++ d.1).length) ∧
    (∀ i ∈ d.2, i < start + ([CGate.cst false] ++ l.1 ++ r.1 ++ d.1).length)
  simp only [List.length_append, List.length_singleton]
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro i hi
    have h := hl i hi
    change i < start + 1 + l.1.length at h
    omega
  · intro i hi
    have h := hr i hi
    change i < start + 1 + l.1.length + r.1.length at h
    omega
  · intro i hi
    have h := hd i hi
    change i < start + 1 + l.1.length + r.1.length + d.1.length at h
    omega

theorem crossProducts_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (x y : FractionRefs) (hx : Valid x vals.length) (hy : Valid y vals.length) :
    let c := crossProducts (n := n) vals.length x y
    let out := runFrom a vals c.1
    out.getD vals.length false = false ∧
      wordValue out c.2.left = wordValue vals x.numerator * wordValue vals y.denominator ∧
      wordValue out c.2.right = wordValue vals y.numerator * wordValue vals x.denominator ∧
      wordValue out c.2.denominator = wordValue vals x.denominator * wordValue vals y.denominator := by
  let v0 := runFrom a vals [CGate.cst false]
  have hl0 : v0.length = vals.length + 1 := by simp only [v0, runFrom_length, List.length_singleton]
  have hz0 : vals.length < v0.length := by rw [hl0]; omega
  have hzero0 : v0.getD vals.length false = false := by
    simp only [v0, runFrom, evalGate, read_append_start, List.getD_cons_zero]
  have hx0 := hx.mono (show vals.length ≤ v0.length by omega)
  have hy0 := hy.mono (show vals.length ≤ v0.length by omega)
  let l := productBits (n := n) v0.length vals.length x.numerator y.denominator
  let v1 := runFrom a v0 l.1
  have hl1 : v1.length = v0.length + l.1.length := runFrom_length _ _ _
  have hz1 : vals.length < v1.length := by omega
  have hzero1 : v1.getD vals.length false = false := (read_runFrom_old a v0 l.1 _ hz0).trans hzero0
  have hx1 := hx0.mono (show v0.length ≤ v1.length by omega)
  have hy1 := hy0.mono (show v0.length ≤ v1.length by omega)
  let r := productBits (n := n) v1.length vals.length y.numerator x.denominator
  let v2 := runFrom a v1 r.1
  have hl2 : v2.length = v1.length + r.1.length := runFrom_length _ _ _
  have hz2 : vals.length < v2.length := by omega
  have hzero2 : v2.getD vals.length false = false := (read_runFrom_old a v1 r.1 _ hz1).trans hzero1
  have hx2 := hx1.mono (show v1.length ≤ v2.length by omega)
  have hy2 := hy1.mono (show v1.length ≤ v2.length by omega)
  let d := productBits (n := n) v2.length vals.length x.denominator y.denominator
  let v3 := runFrom a v2 d.1
  have heq : crossProducts (n := n) vals.length x y =
      ([.cst false] ++ l.1 ++ r.1 ++ d.1, ⟨l.2, r.2, d.2⟩) := by
    simp only [crossProducts, d, r, l, hl2, hl1, hl0]
  have hphase : runFrom a vals (crossProducts (n := n) vals.length x y).1 = v3 := by
    rw [heq]
    simp only [runFrom_append]
    rfl
  have hleft1 : ∀ i ∈ l.2, i < v1.length := by rw [hl1]; exact productBits_refs_lt _ _ _ _ hz0
  have hleft2 : ∀ i ∈ l.2, i < v2.length := by intro i hi; have h := hleft1 i hi; omega
  have hright2 : ∀ i ∈ r.2, i < v2.length := by rw [hl2]; exact productBits_refs_lt _ _ _ _ hz1
  have hlval := productBits_spec a v0 vals.length x.numerator y.denominator hz0 hzero0 hx0.2.1 hy0.2.2
  have hrval := productBits_spec a v1 vals.length y.numerator x.denominator hz1 hzero1 hy1.2.1 hx1.2.2
  have hdval := productBits_spec a v2 vals.length x.denominator y.denominator hz2 hzero2 hx2.2.2 hy2.2.2
  have old1 (word : List ℕ) (hw : ∀ i ∈ word, i < vals.length) : wordValue v1 word = wordValue vals word := by
    rw [wordValue_runFrom_old a v0 l.1 word (by intro i hi; have h := hw i hi; omega)]
    exact wordValue_runFrom_old a vals [CGate.cst false] word hw
  have old2 (word : List ℕ) (hw : ∀ i ∈ word, i < vals.length) : wordValue v2 word = wordValue vals word := by
    rw [wordValue_runFrom_old a v1 r.1 word (by intro i hi; have h := hw i hi; omega)]
    exact old1 word hw
  dsimp only
  rw [hphase, heq]
  change v3.getD vals.length false = false ∧
    wordValue v3 l.2 = _ ∧ wordValue v3 r.2 = _ ∧ wordValue v3 d.2 = _
  refine ⟨(read_runFrom_old a v2 d.1 _ hz2).trans hzero2, ?_, ?_, ?_⟩
  · rw [wordValue_runFrom_old a v2 d.1 l.2 hleft2, wordValue_runFrom_old a v1 r.1 l.2 hleft1]
    change wordValue v1 l.2 = _ at hlval
    rw [wordValue_runFrom_old a vals [CGate.cst false] x.numerator hx.2.1,
      wordValue_runFrom_old a vals [CGate.cst false] y.denominator hy.2.2] at hlval
    exact hlval
  · rw [wordValue_runFrom_old a v2 d.1 r.2 hright2]
    change wordValue v2 r.2 = _ at hrval
    rw [old1 y.numerator hy.2.1, old1 x.denominator hx.2.2] at hrval
    exact hrval
  · change wordValue v3 d.2 = _ at hdval
    rw [old2 x.denominator hx.2.2, old2 y.denominator hy.2.2] at hdval
    exact hdval

def combineSigned {n : ℕ} (subtract : Bool) (start sx : ℕ) (xs : List ℕ)
    (sy : ℕ) (ys : List ℕ) : List (CGate n) × (ℕ × List ℕ) :=
  if subtract then subtractSigned start sx xs sy ys else addSigned start sx xs sy ys

theorem combineSigned_word_length {n : ℕ} (subtract : Bool) (start sx : ℕ)
    (xs : List ℕ) (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (combineSigned (n := n) subtract start sx xs sy ys).2.2.length = xs.length + 1 := by
  cases subtract
  · exact addSigned_word_length _ _ _ _ _ hlen
  · exact subtractSigned_word_length _ _ _ _ _ hlen

theorem combineSigned_gate_count {n : ℕ} (subtract : Bool) (start sx : ℕ)
    (xs : List ℕ) (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (combineSigned (n := n) subtract start sx xs sy ys).1.length ≤ 27 * xs.length + 8 := by
  cases subtract
  · simpa only [combineSigned, Bool.false_eq_true, ↓reduceIte, addSigned_gate_count _ _ _ _ _ hlen] using
      (show 27 * xs.length + 7 ≤ 27 * xs.length + 8 by omega)
  · exact le_of_eq (subtractSigned_gate_count _ _ _ _ _ hlen)

theorem combineSigned_refs_lt {n : ℕ} (subtract : Bool) (start sx : ℕ)
    (xs : List ℕ) (sy : ℕ) (ys : List ℕ) (hlen : xs.length = ys.length) :
    (combineSigned (n := n) subtract start sx xs sy ys).2.1 <
        start + (combineSigned (n := n) subtract start sx xs sy ys).1.length ∧
      ∀ i ∈ (combineSigned (n := n) subtract start sx xs sy ys).2.2,
        i < start + (combineSigned (n := n) subtract start sx xs sy ys).1.length := by
  cases subtract
  · exact addSigned_refs_lt _ _ _ _ _ hlen
  · exact subtractSigned_refs_lt _ _ _ _ _ hlen

theorem combineSigned_spec {n : ℕ} (subtract : Bool) (a : Fin n → Bool)
    (vals : List Bool) (sx : ℕ) (xs : List ℕ) (sy : ℕ) (ys : List ℕ)
    (hlen : xs.length = ys.length) (hsx : sx < vals.length) (hsy : sy < vals.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length) :
    let code := combineSigned (n := n) subtract vals.length sx xs sy ys
    signedValue (runFrom a vals code.1) code.2.1 code.2.2 =
      if subtract then signedValue vals sx xs - signedValue vals sy ys
      else signedValue vals sx xs + signedValue vals sy ys := by
  cases subtract
  · exact addSigned_spec a vals sx xs sy ys hlen hsx hsy hx hy
  · exact subtractSigned_spec a vals sx xs sy ys hlen hsx hsy hx hy

def combineFractions {n : ℕ} (subtract : Bool) (start : ℕ) (x y : FractionRefs) :
    List (CGate n) × FractionRefs :=
  let cross := crossProducts start x y
  let num := combineSigned subtract (start + cross.1.length) x.sign cross.2.left y.sign cross.2.right
  let norm := normalizeWords (start + cross.1.length + num.1.length)
    num.2.2 (cross.2.denominator ++ [start])
  (cross.1 ++ num.1 ++ norm.1, ⟨num.2.1, norm.2.1, norm.2.2⟩)

def addFractions {n : ℕ} (start : ℕ) (x y : FractionRefs) : List (CGate n) × FractionRefs :=
  combineFractions false start x y

def subtractFractions {n : ℕ} (start : ℕ) (x y : FractionRefs) : List (CGate n) × FractionRefs :=
  combineFractions true start x y

theorem combineFractions_width {n : ℕ} (subtract : Bool) (start : ℕ)
    (x y : FractionRefs) (w : ℕ) (hx : Width x w) (hy : Width y w) :
    Width (combineFractions (n := n) subtract start x y).2 (2 * w + 1) := by
  let cross := crossProducts (n := n) start x y
  let num := combineSigned (n := n) subtract (start + cross.1.length) x.sign cross.2.left y.sign cross.2.right
  have hl := crossProducts_lengths (n := n) start x y w hx hy
  change cross.2.left.length = _ ∧ cross.2.right.length = _ ∧ cross.2.denominator.length = _ at hl
  have hn : num.2.2.length = 2 * w + 1 := by
    rw [combineSigned_word_length _ _ _ _ _ _ (hl.1.trans hl.2.1.symm), hl.1]
  have hd : (cross.2.denominator ++ [start]).length = 2 * w + 1 := by simp only [List.length_append, List.length_singleton, hl.2.2]
  exact (normalizeWords_lengths (n := n) (start + cross.1.length + num.1.length)
    num.2.2 (cross.2.denominator ++ [start]) (hn.trans hd.symm)).imp
    (fun h => h.trans hn) (fun h => h.trans hn)

theorem combineFractions_gate_count {n : ℕ} (subtract : Bool) (start : ℕ)
    (x y : FractionRefs) (w : ℕ) (hx : Width x w) (hy : Width y w) :
    (combineFractions (n := n) subtract start x y).1.length ≤ 1024 * (w + 1) ^ 3 := by
  let cross := crossProducts (n := n) start x y
  let num := combineSigned (n := n) subtract (start + cross.1.length) x.sign cross.2.left y.sign cross.2.right
  let norm := normalizeWords (n := n) (start + cross.1.length + num.1.length)
    num.2.2 (cross.2.denominator ++ [start])
  have hl := crossProducts_lengths (n := n) start x y w hx hy
  change cross.2.left.length = _ ∧ cross.2.right.length = _ ∧ cross.2.denominator.length = _ at hl
  have hn : num.2.2.length = 2 * w + 1 := by
    rw [combineSigned_word_length _ _ _ _ _ _ (hl.1.trans hl.2.1.symm), hl.1]
  have hd : (cross.2.denominator ++ [start]).length = 2 * w + 1 := by simp only [List.length_append, List.length_singleton, hl.2.2]
  have hc := crossProducts_gate_count (n := n) start x y w hx hy
  have hs := combineSigned_gate_count (n := n) subtract (start + cross.1.length)
    x.sign cross.2.left y.sign cross.2.right (hl.1.trans hl.2.1.symm)
  rw [hl.1] at hs
  have hm := normalizeWords_gate_count (n := n) (start + cross.1.length + num.1.length)
    num.2.2 (cross.2.denominator ++ [start]) (hn.trans hd.symm)
  rw [hn] at hm
  change cross.1.length ≤ _ at hc
  change num.1.length ≤ _ at hs
  change norm.1.length ≤ _ at hm
  have hcube : (2 * w + 1 + 1) ^ 3 = 8 * (w + 1) ^ 3 := by ring
  have hw : w + 1 ≤ (w + 1) ^ 3 := Nat.le_self_pow (by omega) _
  change (cross.1 ++ num.1 ++ norm.1).length ≤ _
  simp only [List.length_append]
  nlinarith

theorem combineFractions_valid {n : ℕ} (subtract : Bool) (start : ℕ)
    (x y : FractionRefs) (w : ℕ) (hx : Width x w) (hy : Width y w) :
    Valid (combineFractions (n := n) subtract start x y).2
      (start + (combineFractions (n := n) subtract start x y).1.length) := by
  let cross := crossProducts (n := n) start x y
  let num := combineSigned (n := n) subtract (start + cross.1.length) x.sign cross.2.left y.sign cross.2.right
  let norm := normalizeWords (n := n) (start + cross.1.length + num.1.length)
    num.2.2 (cross.2.denominator ++ [start])
  have hl := crossProducts_lengths (n := n) start x y w hx hy
  change cross.2.left.length = _ ∧ cross.2.right.length = _ ∧ cross.2.denominator.length = _ at hl
  have hn : num.2.2.length = 2 * w + 1 := by
    rw [combineSigned_word_length _ _ _ _ _ _ (hl.1.trans hl.2.1.symm), hl.1]
  have hd : (cross.2.denominator ++ [start]).length = 2 * w + 1 := by simp only [List.length_append, List.length_singleton, hl.2.2]
  have hc := crossProducts_refs_lt (n := n) start x y
  change start < start + cross.1.length ∧
    (∀ i ∈ cross.2.left, i < start + cross.1.length) ∧
    (∀ i ∈ cross.2.right, i < start + cross.1.length) ∧
    (∀ i ∈ cross.2.denominator, i < start + cross.1.length) at hc
  have hs := combineSigned_refs_lt (n := n) subtract (start + cross.1.length)
    x.sign cross.2.left y.sign cross.2.right (hl.1.trans hl.2.1.symm)
  change num.2.1 < start + cross.1.length + num.1.length ∧
    (∀ i ∈ num.2.2, i < start + cross.1.length + num.1.length) at hs
  have hdr : ∀ i ∈ cross.2.denominator ++ [start], i < start + cross.1.length + num.1.length := by
    intro i hi
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · have h := hc.2.2.2 i hi; omega
    · have h := hc.1; omega
  have hm := normalizeWords_refs_lt (n := n) (start + cross.1.length + num.1.length)
    num.2.2 (cross.2.denominator ++ [start]) (hn.trans hd.symm) hs.2 hdr
  change num.2.1 < start + (cross.1 ++ num.1 ++ norm.1).length ∧
    (∀ i ∈ norm.2.1, i < start + (cross.1 ++ num.1 ++ norm.1).length) ∧
    (∀ i ∈ norm.2.2, i < start + (cross.1 ++ num.1 ++ norm.1).length)
  simp only [List.length_append]
  refine ⟨by have h := hs.1; omega, ?_, ?_⟩
  · intro i hi
    have h := hm.1 i hi
    change i < start + cross.1.length + num.1.length + norm.1.length at h
    omega
  · intro i hi
    have h := hm.2 i hi
    change i < start + cross.1.length + num.1.length + norm.1.length at h
    omega

private theorem signedMagnitude_scale (b : Bool) (m d : ℕ) :
    signedMagnitude b (m * d) = signedMagnitude b m * (d : ℤ) := by
  cases b <;> simp [signedMagnitude]

set_option maxHeartbeats 2000000 in
theorem combineFractions_represents {n : ℕ} (subtract : Bool) (a : Fin n → Bool)
    (vals : List Bool) (x y : FractionRefs) (q r : ℚ) (w : ℕ)
    (hxw : Width x w) (hyw : Width y w)
    (hxv : Valid x vals.length) (hyv : Valid y vals.length)
    (hx : Represents vals x q) (hy : Represents vals y r) :
    Represents (runFrom a vals (combineFractions subtract vals.length x y).1)
      (combineFractions (n := n) subtract vals.length x y).2
      (if subtract then q - r else q + r) := by
  let cross := crossProducts (n := n) vals.length x y
  let v1 := runFrom a vals cross.1
  have hl1 : v1.length = vals.length + cross.1.length := runFrom_length _ _ _
  have hcross := crossProducts_spec a vals x y hxv hyv
  dsimp only at hcross
  change v1.getD vals.length false = false ∧
    wordValue v1 cross.2.left = _ ∧ wordValue v1 cross.2.right = _ ∧
      wordValue v1 cross.2.denominator = _ at hcross
  have hcl := crossProducts_lengths (n := n) vals.length x y w hxw hyw
  change cross.2.left.length = _ ∧ cross.2.right.length = _ ∧ cross.2.denominator.length = _ at hcl
  have hcr := crossProducts_refs_lt (n := n) vals.length x y
  rw [← hl1] at hcr
  have hxv1 := hxv.mono (show vals.length ≤ v1.length by omega)
  have hyv1 := hyv.mono (show vals.length ≤ v1.length by omega)
  let num := combineSigned (n := n) subtract v1.length x.sign cross.2.left y.sign cross.2.right
  let v2 := runFrom a v1 num.1
  have hl2 : v2.length = v1.length + num.1.length := runFrom_length _ _ _
  have hnr := combineSigned_refs_lt (n := n) subtract v1.length x.sign cross.2.left
    y.sign cross.2.right (hcl.1.trans hcl.2.1.symm)
  change num.2.1 < v1.length + num.1.length ∧
    (∀ i ∈ num.2.2, i < v1.length + num.1.length) at hnr
  rw [← hl2] at hnr
  have hnl : num.2.2.length = 2 * w + 1 := by
    rw [combineSigned_word_length _ _ _ _ _ _ (hcl.1.trans hcl.2.1.symm), hcl.1]
  let raw : FractionRefs := ⟨num.2.1, num.2.2, cross.2.denominator ++ [vals.length]⟩
  have hrawvalid : Valid raw v2.length := by
    refine ⟨hnr.1, hnr.2, ?_⟩
    intro i hi
    simp only [raw, List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · have h := hcr.2.2.2 i hi; omega
    · have h := hcr.1; omega
  have hrawlen : raw.numerator.length = raw.denominator.length := by
    simp only [raw, hnl, List.length_append, List.length_singleton, hcl.2.2]
  have hsx : v1.getD x.sign false = vals.getD x.sign false := read_runFrom_old a vals cross.1 _ hxv.1
  have hsy : v1.getD y.sign false = vals.getD y.sign false := read_runFrom_old a vals cross.1 _ hyv.1
  have hleft : signedValue v1 x.sign cross.2.left = q.num * r.den := by
    rw [signedValue, hsx, hcross.2.1, signedMagnitude_scale]
    exact congrArg₂ (· * ·) hx.1 (congrArg (fun d : ℕ => (d : ℤ)) hy.2)
  have hright : signedValue v1 y.sign cross.2.right = r.num * q.den := by
    rw [signedValue, hsy, hcross.2.2.1, signedMagnitude_scale]
    exact congrArg₂ (· * ·) hy.1 (congrArg (fun d : ℕ => (d : ℤ)) hx.2)
  have hnum := combineSigned_spec subtract a v1 x.sign cross.2.left y.sign cross.2.right
    (hcl.1.trans hcl.2.1.symm) hxv1.1 hyv1.1 hcr.2.1 hcr.2.2.1
  dsimp only at hnum
  rw [hleft, hright] at hnum
  let f := if subtract then rawSub q r else rawAdd q r
  have hrawnum : signedValue v2 raw.sign raw.numerator = f.numerator := by
    change signedValue v2 num.2.1 num.2.2 = _
    change signedValue v2 num.2.1 num.2.2 = _ at hnum
    rw [hnum]
    cases subtract <;> rfl
  have hrawden : wordValue v2 raw.denominator = f.denominator := by
    change wordValue v2 (cross.2.denominator ++ [vals.length]) = _
    have hzero : v2.getD vals.length false = false :=
      (read_runFrom_old a v1 num.1 vals.length hcr.1).trans hcross.1
    rw [wordValue_append, wordValue_runFrom_old a v1 num.1 cross.2.denominator hcr.2.2.2,
      hcross.2.2.2, hx.2, hy.2]
    simp only [wordValue, hzero, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
    cases subtract <;> rfl
  let norm := normalizeWords (n := n) v2.length raw.numerator raw.denominator
  have hnorm := normalizeWords_represents a v2 raw hrawlen hrawvalid f hrawnum hrawden
  have hf : f.normalize = (if subtract then q - r else q + r) := by
    cases subtract <;> simp [f]
  rw [hf] at hnorm
  have heq : combineFractions (n := n) subtract vals.length x y =
      (cross.1 ++ num.1 ++ norm.1, ⟨num.2.1, norm.2.1, norm.2.2⟩) := by
    simp only [combineFractions, norm, raw, num, hl2, hl1, cross]
  rw [heq]
  change Represents (runFrom a vals (cross.1 ++ num.1 ++ norm.1)) _ _
  rw [runFrom_append, runFrom_append]
  exact hnorm

theorem addFractions_width {n : ℕ} (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    Width (addFractions (n := n) start x y).2 (2 * w + 1) :=
  combineFractions_width false start x y w hx hy

theorem subtractFractions_width {n : ℕ} (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    Width (subtractFractions (n := n) start x y).2 (2 * w + 1) :=
  combineFractions_width true start x y w hx hy

theorem addFractions_gate_count {n : ℕ} (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    (addFractions (n := n) start x y).1.length ≤ 1024 * (w + 1) ^ 3 :=
  combineFractions_gate_count false start x y w hx hy

theorem subtractFractions_gate_count {n : ℕ} (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    (subtractFractions (n := n) start x y).1.length ≤ 1024 * (w + 1) ^ 3 :=
  combineFractions_gate_count true start x y w hx hy

theorem addFractions_valid {n : ℕ} (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    Valid (addFractions (n := n) start x y).2 (start + (addFractions (n := n) start x y).1.length) :=
  combineFractions_valid false start x y w hx hy

theorem subtractFractions_valid {n : ℕ} (start : ℕ) (x y : FractionRefs) (w : ℕ)
    (hx : Width x w) (hy : Width y w) :
    Valid (subtractFractions (n := n) start x y).2 (start + (subtractFractions (n := n) start x y).1.length) :=
  combineFractions_valid true start x y w hx hy

theorem addFractions_represents {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (x y : FractionRefs) (q r : ℚ) (w : ℕ)
    (hxw : Width x w) (hyw : Width y w) (hxv : Valid x vals.length) (hyv : Valid y vals.length)
    (hx : Represents vals x q) (hy : Represents vals y r) :
    Represents (runFrom a vals (addFractions vals.length x y).1)
      (addFractions (n := n) vals.length x y).2 (q + r) :=
  combineFractions_represents false a vals x y q r w hxw hyw hxv hyv hx hy

theorem subtractFractions_represents {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (x y : FractionRefs) (q r : ℚ) (w : ℕ)
    (hxw : Width x w) (hyw : Width y w) (hxv : Valid x vals.length) (hyv : Valid y vals.length)
    (hx : Represents vals x q) (hy : Represents vals y r) :
    Represents (runFrom a vals (subtractFractions vals.length x y).1)
      (subtractFractions (n := n) vals.length x y).2 (q - r) :=
  combineFractions_represents true a vals x y q r w hxw hyw hxv hyv hx hy

end GodMoveBinaryRationalAdd

#print axioms GodMoveBinaryRationalAdd.crossProducts_spec
#print axioms GodMoveBinaryRationalAdd.crossProducts_gate_count
#print axioms GodMoveBinaryRationalAdd.combineFractions_represents
#print axioms GodMoveBinaryRationalAdd.addFractions_width
#print axioms GodMoveBinaryRationalAdd.addFractions_gate_count
#print axioms GodMoveBinaryRationalAdd.addFractions_valid
#print axioms GodMoveBinaryRationalAdd.addFractions_represents
#print axioms GodMoveBinaryRationalAdd.subtractFractions_width
#print axioms GodMoveBinaryRationalAdd.subtractFractions_gate_count
#print axioms GodMoveBinaryRationalAdd.subtractFractions_valid
#print axioms GodMoveBinaryRationalAdd.subtractFractions_represents
