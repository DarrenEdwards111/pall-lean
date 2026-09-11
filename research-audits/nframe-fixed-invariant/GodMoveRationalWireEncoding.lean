import GodMoveBinaryFractionNormalize
import GodMoveBinaryMultiply

/-!
# Canonical rational values represented by Boolean wires

The representation keeps a sign reference and two unsigned words. Correctness
specifies the canonical integer numerator and positive denominator separately;
negative zero is permitted because its decoded integer is still zero.
-/

namespace GodMoveRationalWireEncoding

open GodMoveBinaryAdder GodMoveBinaryFractionNormalize GodMoveRationalPrimitiveBounds
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer

def signedMagnitude (negative : Bool) (magnitude : ℕ) : ℤ :=
  if negative then -(magnitude : ℤ) else (magnitude : ℤ)

def signedValue (vals : List Bool) (sign : ℕ) (word : List ℕ) : ℤ :=
  signedMagnitude (vals.getD sign false) (wordValue vals word)

@[simp] theorem signedMagnitude_natAbs (b : Bool) (m : ℕ) :
    (signedMagnitude b m).natAbs = m := by cases b <;> simp [signedMagnitude]

@[simp] theorem signedValue_natAbs (vals : List Bool) (sign : ℕ) (word : List ℕ) :
    (signedValue vals sign word).natAbs = wordValue vals word :=
  signedMagnitude_natAbs _ _

theorem signedMagnitude_mul (a b : Bool) (m n : ℕ) :
    signedMagnitude (a ^^ b) (m * n) = signedMagnitude a m * signedMagnitude b n := by
  cases a <;> cases b <;> simp [signedMagnitude]

theorem signedValue_runFrom_old {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (code : List (CGate n)) (sign : ℕ) (word : List ℕ)
    (hs : sign < vals.length) (hw : ∀ i ∈ word, i < vals.length) :
    signedValue (runFrom a vals code) sign word = signedValue vals sign word := by
  simp only [signedValue, read_runFrom_old a vals code sign hs,
    wordValue_runFrom_old a vals code word hw]

structure FractionRefs where
  sign : ℕ
  numerator : List ℕ
  denominator : List ℕ
  deriving Repr, DecidableEq

def FractionRefs.value (r : FractionRefs) (vals : List Bool) : ℚ :=
  (signedValue vals r.sign r.numerator : ℚ) / wordValue vals r.denominator

def Represents (vals : List Bool) (r : FractionRefs) (q : ℚ) : Prop :=
  signedValue vals r.sign r.numerator = q.num ∧ wordValue vals r.denominator = q.den

def Valid (r : FractionRefs) (start : ℕ) : Prop :=
  r.sign < start ∧ (∀ i ∈ r.numerator, i < start) ∧ (∀ i ∈ r.denominator, i < start)

def Width (r : FractionRefs) (w : ℕ) : Prop :=
  r.numerator.length = w ∧ r.denominator.length = w

theorem Valid.mono {r : FractionRefs} {s t : ℕ} (h : Valid r s) (hst : s ≤ t) :
    Valid r t := ⟨h.1.trans_le hst, fun i hi => (h.2.1 i hi).trans_le hst,
      fun i hi => (h.2.2 i hi).trans_le hst⟩

theorem Represents.value_eq {vals : List Bool} {r : FractionRefs} {q : ℚ}
    (h : Represents vals r q) : r.value vals = q := by
  rw [FractionRefs.value, h.1, h.2, Rat.num_div_den]

theorem Represents.magnitude {vals : List Bool} {r : FractionRefs} {q : ℚ}
    (h : Represents vals r q) : wordValue vals r.numerator = q.num.natAbs := by
  rw [← h.1, signedValue_natAbs]

theorem Represents.denominator_pos {vals : List Bool} {r : FractionRefs} {q : ℚ}
    (h : Represents vals r q) : 0 < wordValue vals r.denominator := by
  rw [h.2]
  exact q.den_pos

theorem Represents.runFrom_old {n : ℕ} {vals : List Bool} {r : FractionRefs} {q : ℚ}
    (h : Represents vals r q) (a : Fin n → Bool) (code : List (CGate n))
    (hv : Valid r vals.length) : Represents (runFrom a vals code) r q := by
  constructor
  · exact (signedValue_runFrom_old a vals code r.sign r.numerator hv.1 hv.2.1).trans h.1
  · exact (wordValue_runFrom_old a vals code r.denominator hv.2.2).trans h.2

theorem signedMagnitude_sign_div (b : Bool) (m d : ℕ) :
    (signedMagnitude b m).sign * (m / d : ℕ) = signedMagnitude b (m / d) := by
  cases m with
  | zero => cases b <;> simp [signedMagnitude]
  | succ m =>
    cases b with
    | false => simp [signedMagnitude]
    | true =>
      have hs : (-(m + 1 : ℕ) : ℤ).sign = -1 :=
        Int.sign_eq_neg_one_of_neg (by omega)
      simp only [signedMagnitude, ↓reduceIte, hs, neg_one_mul]

theorem normalize_same_sign (f : RawFraction) (b : Bool) (m : ℕ)
    (h : f.numerator = signedMagnitude b m) :
    signedMagnitude b f.normalize.num.natAbs = f.normalize.num := by
  rw [normalize_numerator_magnitude, normalize_signed_numerator, h, signedMagnitude_natAbs]
  exact (signedMagnitude_sign_div b m (cancellationDivisor f)).symm

/-- The normalization circuit preserves the existing sign reference and returns
the canonical integer numerator and denominator, including a zero numerator. -/
theorem normalizeWords_represents {n : ℕ} (a : Fin n → Bool) (vals : List Bool)
    (r : FractionRefs) (hlen : r.numerator.length = r.denominator.length)
    (hv : Valid r vals.length) (f : RawFraction)
    (hnum : signedValue vals r.sign r.numerator = f.numerator)
    (hden : wordValue vals r.denominator = f.denominator) :
    Represents (runFrom a vals (normalizeWords vals.length r.numerator r.denominator).1)
      ⟨r.sign, (normalizeWords (n := n) vals.length r.numerator r.denominator).2.1,
        (normalizeWords (n := n) vals.length r.numerator r.denominator).2.2⟩ f.normalize := by
  have hm : wordValue vals r.numerator = f.numerator.natAbs := by
    rw [← hnum, signedValue_natAbs]
  have h := normalizeWords_canonical a vals r.numerator r.denominator hlen hv.2.1 hv.2.2
    f hm hden
  constructor
  · change signedMagnitude _ _ = _
    rw [read_runFrom_old a vals _ r.sign hv.1, h.1]
    exact normalize_same_sign f _ _ hnum.symm
  · exact h.2

/-- Both canonical magnitudes fit a fixed stored word width. -/
def Fits (q : ℚ) (w : ℕ) : Prop := q.num.natAbs < 2 ^ w ∧ q.den < 2 ^ w

theorem fits_of_bitBound {q : ℚ} {b : ℕ}
    (h : GodMoveRationalPrecisionArithmetic.BitBound q b) : Fits q (b + 1) := by
  have hp : 2 ^ b < (2 : ℕ) ^ (b + 1) :=
    Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self b)
  exact ⟨h.1.trans_lt hp, h.2.trans_lt hp⟩

/-- Output words are padded or truncated to the fixed budget. The value theorem
uses a proved precision bound, rather than assuming discarded bits are zero. -/
def resize (r : FractionRefs) (w zeroRef : ℕ) : FractionRefs :=
  ⟨r.sign, (r.numerator ++ List.replicate w zeroRef).take w,
    (r.denominator ++ List.replicate w zeroRef).take w⟩

theorem resize_width (r : FractionRefs) (w zeroRef : ℕ) : Width (resize r w zeroRef) w := by
  constructor <;> simp only [resize, List.length_take, List.length_append, List.length_replicate]
    <;> exact Nat.min_eq_left (Nat.le_add_left _ _)

theorem resize_valid (r : FractionRefs) (w zeroRef start : ℕ)
    (hr : Valid r start) (hz : zeroRef < start) : Valid (resize r w zeroRef) start := by
  refine ⟨hr.1, ?_, ?_⟩
  · intro i hi
    rcases List.mem_append.mp (List.mem_of_mem_take hi) with hi | hi
    · exact hr.2.1 i hi
    · simpa only [List.eq_of_mem_replicate hi] using hz
  · intro i hi
    rcases List.mem_append.mp (List.mem_of_mem_take hi) with hi | hi
    · exact hr.2.2 i hi
    · simpa only [List.eq_of_mem_replicate hi] using hz

theorem resized_word_value (vals : List Bool) (word : List ℕ) (w zeroRef : ℕ)
    (hz : vals.getD zeroRef false = false) (hfit : wordValue vals word < 2 ^ w) :
    wordValue vals ((word ++ List.replicate w zeroRef).take w) = wordValue vals word := by
  have hp := GodMoveWireSum.wordValue_pad_zero vals word zeroRef w hz
  rw [GodMoveBinaryMultiply.wordValue_take_eq_of_lt _ _ _ (hp ▸ hfit), hp]

theorem resize_represents (vals : List Bool) (r : FractionRefs) (q : ℚ) (w zeroRef : ℕ)
    (hr : Represents vals r q) (hz : vals.getD zeroRef false = false) (hf : Fits q w) :
    Represents vals (resize r w zeroRef) q := by
  have hn : wordValue vals r.numerator < 2 ^ w := by rw [hr.magnitude]; exact hf.1
  have hd : wordValue vals r.denominator < 2 ^ w := by rw [hr.2]; exact hf.2
  constructor
  · change signedMagnitude _ _ = _
    dsimp only [resize]
    rw [resized_word_value vals r.numerator w zeroRef hz hn]
    exact hr.1
  · exact (resized_word_value vals r.denominator w zeroRef hz hd).trans hr.2

theorem resize_represents_of_bitBound (vals : List Bool) (r : FractionRefs) (q : ℚ)
    (b zeroRef : ℕ) (hr : Represents vals r q) (hz : vals.getD zeroRef false = false)
    (hq : GodMoveRationalPrecisionArithmetic.BitBound q b) :
    Represents vals (resize r (b + 1) zeroRef) q :=
  resize_represents vals r q (b + 1) zeroRef hr hz (fits_of_bitBound hq)

end GodMoveRationalWireEncoding

#print axioms GodMoveRationalWireEncoding.signedMagnitude_mul
#print axioms GodMoveRationalWireEncoding.signedValue_runFrom_old
#print axioms GodMoveRationalWireEncoding.Represents.value_eq
#print axioms GodMoveRationalWireEncoding.Represents.runFrom_old
#print axioms GodMoveRationalWireEncoding.normalize_same_sign
#print axioms GodMoveRationalWireEncoding.normalizeWords_represents
#print axioms GodMoveRationalWireEncoding.resize_width
#print axioms GodMoveRationalWireEncoding.resize_valid
#print axioms GodMoveRationalWireEncoding.resize_represents_of_bitBound
