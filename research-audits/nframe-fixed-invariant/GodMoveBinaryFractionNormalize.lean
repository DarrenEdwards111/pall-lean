import GodMoveBinaryGCD
import GodMoveRationalPrimitiveBounds

/-!
# Rational normalization by emitted Boolean gates

The circuit computes an unsigned gcd once and uses two restoring divisions to
produce the reduced numerator magnitude and denominator. Its inputs are earlier
wire references of equal width, and the numerator sign is retained separately.
The canonical fraction theorem requires the supplied denominator word to encode
a positive denominator. No gcd, remainder, or division primitive is emitted as
a gate; those natural operations occur in the proved specifications only.

The size bound counts Boolean gates, not compiler or host-machine execution.
-/

namespace GodMoveBinaryFractionNormalize

open GodMoveBinaryAdder GodMoveBinaryDivision GodMoveBinaryGCD
open GodMoveRationalPrimitiveBounds
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

/-- Materialize the gcd circuit once, then reuse its output references in both
quotient circuits. -/
def normalizeWords {n : ℕ} (start : ℕ) (xs ys : List ℕ) :
    List (CGate n) × (List ℕ × List ℕ) :=
  let g := gcdWords start xs ys
  let qn := divideWords (start + g.1.length) xs g.2
  let qd := divideWords (start + g.1.length + qn.1.length) ys g.2
  ((g.1 ++ qn.1) ++ qd.1, (qn.2.1, qd.2.1))

theorem normalizeWords_lengths {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (normalizeWords (n := n) start xs ys).2.1.length = xs.length ∧
      (normalizeWords (n := n) start xs ys).2.2.length = xs.length := by
  have hg := gcdWords_word_length (n := n) start xs ys hlen
  constructor
  · exact (divideWords_lengths _ xs _ hg.symm).1
  · exact ((divideWords_lengths _ ys _ (hlen.symm.trans hg.symm)).1).trans hlen.symm

theorem normalizeWords_gate_count {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) :
    (normalizeWords (n := n) start xs ys).1.length ≤ 96 * (xs.length + 1) ^ 3 := by
  let g := gcdWords (n := n) start xs ys
  let qn := divideWords (n := n) (start + g.1.length) xs g.2
  let qd := divideWords (n := n) (start + g.1.length + qn.1.length) ys g.2
  have hgl : g.2.length = xs.length := gcdWords_word_length start xs ys hlen
  have hg := gcdWords_gate_count (n := n) start xs ys hlen
  have hn := divideWords_gate_count (n := n) (start + g.1.length) xs g.2 hgl.symm
  have hd := divideWords_gate_count (n := n) (start + g.1.length + qn.1.length)
    ys g.2 (hlen.symm.trans hgl.symm)
  change g.1.length ≤ _ at hg
  change qn.1.length ≤ _ at hn
  change qd.1.length ≤ _ at hd
  rw [← hlen] at hd
  change ((g.1 ++ qn.1) ++ qd.1).length ≤ _
  simp only [List.length_append]
  have hp : (xs.length + 1) ^ 2 ≤ (xs.length + 1) ^ 3 := by
    apply Nat.pow_le_pow_right (by omega)
    omega
  omega

theorem normalizeWords_refs_lt {n : ℕ} (start : ℕ) (xs ys : List ℕ)
    (hlen : xs.length = ys.length) (hx : ∀ i ∈ xs, i < start)
    (hy : ∀ i ∈ ys, i < start) :
    (∀ i ∈ (normalizeWords (n := n) start xs ys).2.1,
      i < start + (normalizeWords (n := n) start xs ys).1.length) ∧
    (∀ i ∈ (normalizeWords (n := n) start xs ys).2.2,
      i < start + (normalizeWords (n := n) start xs ys).1.length) := by
  let g := gcdWords (n := n) start xs ys
  let qn := divideWords (n := n) (start + g.1.length) xs g.2
  let qd := divideWords (n := n) (start + g.1.length + qn.1.length) ys g.2
  have hgl : g.2.length = xs.length := gcdWords_word_length start xs ys hlen
  have hg : ∀ i ∈ g.2, i < start + g.1.length :=
    gcdWords_refs_lt start xs ys hlen hx hy
  have hx1 : ∀ i ∈ xs, i < start + g.1.length := by
    intro i hi; exact (hx i hi).trans_le (Nat.le_add_right _ _)
  have hy2 : ∀ i ∈ ys, i < start + g.1.length + qn.1.length := by
    intro i hi; have h := hy i hi; omega
  have hg2 : ∀ i ∈ g.2, i < start + g.1.length + qn.1.length := by
    intro i hi; have h := hg i hi; omega
  have hn := (divideWords_refs_lt (n := n) (start + g.1.length) xs g.2
    hgl.symm hx1 hg).1
  have hd := (divideWords_refs_lt (n := n) (start + g.1.length + qn.1.length)
    ys g.2 (hlen.symm.trans hgl.symm) hy2 hg2).1
  change (∀ i ∈ qn.2.1, i < start + ((g.1 ++ qn.1) ++ qd.1).length) ∧
    (∀ i ∈ qd.2.1, i < start + ((g.1 ++ qn.1) ++ qd.1).length)
  simp only [List.length_append]
  constructor
  · intro i hi
    have h := hn i hi
    change i < start + g.1.length + qn.1.length at h
    omega
  · intro i hi
    have h := hd i hi
    change i < start + g.1.length + qn.1.length + qd.1.length at h
    omega

/-- Both quotients are obtained from the same computed gcd. This generic
statement also covers zero words using the divider's totalized convention. -/
theorem normalizeWords_spec {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (xs ys : List ℕ) (hlen : xs.length = ys.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length) :
    wordValue (runFrom a vals (normalizeWords vals.length xs ys).1)
        (normalizeWords (n := n) vals.length xs ys).2.1 =
        wordValue vals xs / Nat.gcd (wordValue vals xs) (wordValue vals ys) ∧
      wordValue (runFrom a vals (normalizeWords vals.length xs ys).1)
        (normalizeWords (n := n) vals.length xs ys).2.2 =
        wordValue vals ys / Nat.gcd (wordValue vals xs) (wordValue vals ys) := by
  let g := gcdWords (n := n) vals.length xs ys
  let v1 := runFrom a vals g.1
  have hl1 : v1.length = vals.length + g.1.length := runFrom_length _ _ _
  let qn := divideWords (n := n) v1.length xs g.2
  let v2 := runFrom a v1 qn.1
  have hl2 : v2.length = v1.length + qn.1.length := runFrom_length _ _ _
  let qd := divideWords (n := n) v2.length ys g.2
  have hgl : g.2.length = xs.length := gcdWords_word_length vals.length xs ys hlen
  have hg1 : ∀ i ∈ g.2, i < v1.length := by
    rw [hl1]
    exact gcdWords_refs_lt _ _ _ hlen hx hy
  have hx1 : ∀ i ∈ xs, i < v1.length := by
    intro i hi; have h := hx i hi; rw [hl1]; omega
  have hy1 : ∀ i ∈ ys, i < v1.length := by
    intro i hi; have h := hy i hi; rw [hl1]; omega
  have hy2 : ∀ i ∈ ys, i < v2.length := by
    intro i hi; have h := hy1 i hi; rw [hl2]; omega
  have hg2 : ∀ i ∈ g.2, i < v2.length := by
    intro i hi; have h := hg1 i hi; rw [hl2]; omega
  have hqn := (divideWords_spec a v1 xs g.2 hgl.symm hx1 hg1).1
  have hqd := (divideWords_spec a v2 ys g.2 (hlen.symm.trans hgl.symm) hy2 hg2).1
  have hqref : ∀ i ∈ qn.2.1, i < v2.length := by
    rw [hl2]
    exact (divideWords_refs_lt _ _ _ hgl.symm hx1 hg1).1
  have hgval : wordValue v1 g.2 = Nat.gcd (wordValue vals xs) (wordValue vals ys) :=
    gcdWords_spec a vals xs ys hlen hx hy
  have hxold : wordValue v1 xs = wordValue vals xs :=
    wordValue_runFrom_old a vals g.1 xs hx
  have hyold : wordValue v2 ys = wordValue vals ys :=
    (wordValue_runFrom_old a v1 qn.1 ys hy1).trans
      (wordValue_runFrom_old a vals g.1 ys hy)
  have hgold : wordValue v2 g.2 = Nat.gcd (wordValue vals xs) (wordValue vals ys) :=
    (wordValue_runFrom_old a v1 qn.1 g.2 hg1).trans hgval
  rw [hxold, hgval] at hqn
  rw [hyold, hgold] at hqd
  have hkeep : wordValue (runFrom a v2 qd.1) qn.2.1 = wordValue v2 qn.2.1 :=
    wordValue_runFrom_old a v2 qd.1 qn.2.1 hqref
  have hout : wordValue (runFrom a v2 qd.1) qn.2.1 =
      wordValue vals xs / Nat.gcd (wordValue vals xs) (wordValue vals ys) ∧
      wordValue (runFrom a v2 qd.1) qd.2.1 =
      wordValue vals ys / Nat.gcd (wordValue vals xs) (wordValue vals ys) :=
    ⟨hkeep.trans hqn, hqd⟩
  simpa only [normalizeWords, g, qn, qd, v1, v2, runFrom_append, runFrom_length] using hout

/-- Separating the sign does not require signed division in the emitted circuit. -/
theorem normalize_signed_numerator (f : RawFraction) :
    f.normalize.num = f.numerator.sign *
      (f.numerator.natAbs / cancellationDivisor f : ℕ) := by
  have hd : (cancellationDivisor f : ℤ) ∣ (f.numerator.natAbs : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
  rw [normalize_numerator]
  conv_lhs => rw [← Int.sign_mul_natAbs f.numerator]
  rw [Int.mul_ediv_assoc _ hd, ← Int.natCast_ediv]

theorem normalize_unsigned_reconstruction (f : RawFraction) :
    ((f.numerator.sign : ℚ) * (f.numerator.natAbs / cancellationDivisor f : ℕ)) /
      (f.denominator / cancellationDivisor f : ℕ) = f.normalize := by
  have h := Rat.num_div_den f.normalize
  rw [normalize_signed_numerator, normalize_denominator, Int.cast_mul, Int.cast_natCast] at h
  exact h

/-- The actual output words equal the canonical numerator magnitude and positive
canonical denominator, for any valid encoding of the raw input fraction. -/
theorem normalizeWords_canonical {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (xs ys : List ℕ) (hlen : xs.length = ys.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length)
    (f : RawFraction) (hnum : wordValue vals xs = f.numerator.natAbs)
    (hden : wordValue vals ys = f.denominator) :
    wordValue (runFrom a vals (normalizeWords vals.length xs ys).1)
        (normalizeWords (n := n) vals.length xs ys).2.1 = f.normalize.num.natAbs ∧
      wordValue (runFrom a vals (normalizeWords vals.length xs ys).1)
        (normalizeWords (n := n) vals.length xs ys).2.2 = f.normalize.den := by
  have h := normalizeWords_spec a vals xs ys hlen hx hy
  simpa only [hnum, hden, normalize_numerator_magnitude, normalize_denominator,
    cancellationDivisor] using h

/-- Decoding the executed output with the original separate numerator sign
recovers the actual normalized rational. -/
theorem normalizeWords_decoded {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (xs ys : List ℕ) (hlen : xs.length = ys.length)
    (hx : ∀ i ∈ xs, i < vals.length) (hy : ∀ i ∈ ys, i < vals.length)
    (f : RawFraction) (hnum : wordValue vals xs = f.numerator.natAbs)
    (hden : wordValue vals ys = f.denominator) :
    ((f.numerator.sign : ℚ) *
        wordValue (runFrom a vals (normalizeWords vals.length xs ys).1)
          (normalizeWords (n := n) vals.length xs ys).2.1) /
      wordValue (runFrom a vals (normalizeWords vals.length xs ys).1)
        (normalizeWords (n := n) vals.length xs ys).2.2 = f.normalize := by
  have h := normalizeWords_spec a vals xs ys hlen hx hy
  rw [h.1, h.2, hnum, hden]
  exact normalize_unsigned_reconstruction f

private def normalizeTwo (x y : List Bool) : ℕ × ℕ :=
  let vals := x ++ y
  let code := normalizeWords (n := 0) vals.length [0, 1] [2, 3]
  let out := runFrom (fun i => Fin.elim0 i) vals code.1
  (wordValue out code.2.1, wordValue out code.2.2)

set_option maxRecDepth 20000 in
example : normalizeTwo [false, true] [false, true] = (1, 1) := by decide

set_option maxRecDepth 20000 in
example : normalizeTwo [false, false] [true, true] = (0, 1) := by decide

end GodMoveBinaryFractionNormalize

#print axioms GodMoveBinaryFractionNormalize.normalizeWords_lengths
#print axioms GodMoveBinaryFractionNormalize.normalizeWords_gate_count
#print axioms GodMoveBinaryFractionNormalize.normalizeWords_refs_lt
#print axioms GodMoveBinaryFractionNormalize.normalizeWords_spec
#print axioms GodMoveBinaryFractionNormalize.normalize_signed_numerator
#print axioms GodMoveBinaryFractionNormalize.normalizeWords_canonical
#print axioms GodMoveBinaryFractionNormalize.normalizeWords_decoded
