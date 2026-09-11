import GodMoveRationalPrecisionArithmetic
import GodMoveEuclideanBitIterations

/-!
# Integer widths for an explicit rational normalization path

The four raw fractions below normalize to the actual rational operations. Their
bounds cover the signed integer products and sums before gcd cancellation, and
all operands of the executed Euclidean algorithm. Exact cancellation cannot
increase either magnitude. This supplies widths for a binary arithmetic backend;
it does not identify these formulas with Lean's optimized native `Rat` execution
or assert a cost for native integer arithmetic.
-/

namespace GodMoveRationalPrimitiveBounds

open GodMoveRationalPrecisionArithmetic

structure RawFraction where
  numerator : ℤ
  denominator : ℕ
  positive : 0 < denominator

def RawFraction.normalize (f : RawFraction) : ℚ :=
  Rat.normalize f.numerator f.denominator (Nat.ne_of_gt f.positive)

def Magnitude (f : RawFraction) (e : ℕ) : Prop :=
  f.numerator.natAbs ≤ 2 ^ e ∧ f.denominator ≤ 2 ^ e

def rawAdd (q r : ℚ) : RawFraction :=
  ⟨q.num * r.den + r.num * q.den, q.den * r.den, by positivity⟩

def rawSub (q r : ℚ) : RawFraction :=
  ⟨q.num * r.den - r.num * q.den, q.den * r.den, by positivity⟩

def rawMul (q r : ℚ) : RawFraction :=
  ⟨q.num * r.num, q.den * r.den, by positivity⟩

/-- Reciprocal sign/field exchange includes the totalized zero convention. -/
def rawDiv (q r : ℚ) : RawFraction := rawMul q r⁻¹

@[simp] theorem normalize_rawAdd (q r : ℚ) : (rawAdd q r).normalize = q + r :=
  (Rat.add_def q r).symm

@[simp] theorem normalize_rawSub (q r : ℚ) : (rawSub q r).normalize = q - r :=
  (Rat.sub_def q r).symm

@[simp] theorem normalize_rawMul (q r : ℚ) : (rawMul q r).normalize = q * r :=
  (Rat.mul_def q r).symm

@[simp] theorem normalize_rawDiv (q r : ℚ) : (rawDiv q r).normalize = q / r := by
  simp [rawDiv, div_eq_mul_inv]

theorem rawDiv_numerator (q r : ℚ) :
    (rawDiv q r).numerator = q.num * (r.num.sign * r.den) := by
  simp [rawDiv, rawMul, Rat.num_inv]

theorem rawDiv_denominator (q r : ℚ) :
    (rawDiv q r).denominator = q.den * (if r.num = 0 then 1 else r.num.natAbs) := by
  simp [rawDiv, rawMul, Rat.den_inv]

/-- The individual cross products are bounded before addition or subtraction. -/
theorem cross_products_bound {q r : ℚ} {b c : ℕ}
    (hq : BitBound q b) (hr : BitBound r c) :
    (q.num * r.den).natAbs ≤ 2 ^ (b + c) ∧
      (r.num * q.den).natAbs ≤ 2 ^ (b + c) ∧
      q.den * r.den ≤ 2 ^ (b + c) := by
  simp only [Int.natAbs_mul, Int.natAbs_natCast, pow_add]
  exact ⟨Nat.mul_le_mul hq.1 hr.2,
    by simpa [Nat.mul_comm] using Nat.mul_le_mul hr.1 hq.2,
    Nat.mul_le_mul hq.2 hr.2⟩

theorem rawAdd_magnitude {q r : ℚ} {b c : ℕ}
    (hq : BitBound q b) (hr : BitBound r c) :
    Magnitude (rawAdd q r) (b + c + 1) := by
  have h := cross_products_bound hq hr
  constructor
  · change (q.num * r.den + r.num * q.den).natAbs ≤ _
    have ht := Int.natAbs_add_le (q.num * r.den) (r.num * q.den)
    rw [pow_succ]
    omega
  · change q.den * r.den ≤ _
    exact h.2.2.trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem rawSub_magnitude {q r : ℚ} {b c : ℕ}
    (hq : BitBound q b) (hr : BitBound r c) :
    Magnitude (rawSub q r) (b + c + 1) := by
  have h := cross_products_bound hq hr
  constructor
  · change (q.num * r.den - r.num * q.den).natAbs ≤ _
    have ht := Int.natAbs_add_le (q.num * r.den) (-(r.num * q.den))
    simp only [Int.natAbs_neg, ← sub_eq_add_neg] at ht
    rw [pow_succ]
    omega
  · change q.den * r.den ≤ _
    exact h.2.2.trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem rawMul_magnitude {q r : ℚ} {b c : ℕ}
    (hq : BitBound q b) (hr : BitBound r c) :
    Magnitude (rawMul q r) (b + c) := by
  constructor
  · simpa only [rawMul, Int.natAbs_mul, pow_add] using Nat.mul_le_mul hq.1 hr.1
  · simpa only [rawMul, pow_add] using Nat.mul_le_mul hq.2 hr.2

theorem reciprocal_bitBound {q : ℚ} {b : ℕ} (hq : BitBound q b) :
    BitBound q⁻¹ b := by
  have hp : 1 ≤ 2 ^ b := Nat.one_le_pow _ _ (by decide)
  simpa only [BitBound, max_eq_right hp] using Bound.inv hq

theorem rawDiv_magnitude {q r : ℚ} {b c : ℕ}
    (hq : BitBound q b) (hr : BitBound r c) :
    Magnitude (rawDiv q r) (b + c) :=
  rawMul_magnitude hq (reciprocal_bitBound hr)

def cancellationDivisor (f : RawFraction) : ℕ :=
  Nat.gcd f.numerator.natAbs f.denominator

theorem cancellationDivisor_pos (f : RawFraction) : 0 < cancellationDivisor f :=
  Nat.gcd_pos_of_pos_right _ f.positive

theorem cancellation_exact (f : RawFraction) :
    (cancellationDivisor f : ℤ) ∣ f.numerator ∧
      cancellationDivisor f ∣ f.denominator :=
  ⟨Int.ofNat_dvd_left.mpr (Nat.gcd_dvd_left _ _), Nat.gcd_dvd_right _ _⟩

theorem normalize_numerator (f : RawFraction) :
    f.normalize.num = f.numerator / (cancellationDivisor f : ℤ) :=
  Rat.num_normalize _

theorem normalize_denominator (f : RawFraction) :
    f.normalize.den = f.denominator / cancellationDivisor f :=
  Rat.den_normalize _

theorem normalize_numerator_magnitude (f : RawFraction) :
    f.normalize.num.natAbs = f.numerator.natAbs / cancellationDivisor f := by
  rw [normalize_numerator, Int.natAbs_ediv_of_dvd (cancellation_exact f).1,
    Int.natAbs_natCast]

/-- The divisions in normalization are exact, including a zero numerator. -/
theorem cancellation_remainders_zero (f : RawFraction) :
    f.numerator % (cancellationDivisor f : ℤ) = 0 ∧
      f.denominator % cancellationDivisor f = 0 :=
  ⟨Int.emod_eq_zero_of_dvd (cancellation_exact f).1,
    Nat.mod_eq_zero_of_dvd (cancellation_exact f).2⟩

theorem normalization_non_growth (f : RawFraction) :
    f.normalize.num.natAbs ≤ f.numerator.natAbs ∧
      f.normalize.den ≤ f.denominator ∧
      cancellationDivisor f ≤ f.denominator := by
  rw [normalize_numerator_magnitude, normalize_denominator]
  exact ⟨Nat.div_le_self _ _, Nat.div_le_self _ _, Nat.gcd_le_right _ f.positive⟩

theorem normalize_zero (f : RawFraction) (h : f.numerator = 0) :
    f.normalize = 0 := by
  unfold RawFraction.normalize
  simp [h]

theorem normalize_zero_components (f : RawFraction) (h : f.numerator = 0) :
    f.normalize.num = 0 ∧ f.normalize.den = 1 := by
  simp [normalize_zero f h]

theorem Magnitude.normalize_bitBound {f : RawFraction} {e : ℕ} (h : Magnitude f e) :
    BitBound f.normalize e :=
  ⟨(normalization_non_growth f).1.trans h.1,
    (normalization_non_growth f).2.1.trans h.2⟩

theorem size_le_of_magnitude {a e : ℕ} (h : a ≤ 2 ^ e) : a.size ≤ e + 1 :=
  Nat.size_le.mpr (h.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self e)))

theorem Magnitude.raw_sizes {f : RawFraction} {e : ℕ} (h : Magnitude f e) :
    f.numerator.natAbs.size ≤ e + 1 ∧ f.denominator.size ≤ e + 1 :=
  ⟨size_le_of_magnitude h.1, size_le_of_magnitude h.2⟩

/-- Both cancellation dividends, the positive divisor, and both quotients fit
within the raw magnitude width. The sign of the numerator is separate. -/
theorem Magnitude.cancellation_sizes {f : RawFraction} {e : ℕ} (h : Magnitude f e) :
    (cancellationDivisor f).size ≤ e + 1 ∧
      f.normalize.num.natAbs.size ≤ e + 1 ∧ f.normalize.den.size ≤ e + 1 := by
  exact ⟨size_le_of_magnitude ((normalization_non_growth f).2.2.trans h.2),
    h.normalize_bitBound.canonical_sizes⟩

/-- The actual executed Euclidean algorithm computes the cancellation divisor. -/
def normalizationGcd (f : RawFraction) : GodMoveEuclideanBitIterations.EuclidResult :=
  GodMoveEuclideanBitIterations.gcd f.numerator.natAbs f.denominator

theorem normalizationGcd_correct (f : RawFraction) :
    (normalizationGcd f).value = cancellationDivisor f ∧
      (normalizationGcd f).finished = true :=
  ⟨GodMoveEuclideanBitIterations.gcd_value _ _,
    GodMoveEuclideanBitIterations.gcd_finished _ _⟩

theorem Magnitude.normalizationGcd_divisions {f : RawFraction} {e : ℕ}
    (h : Magnitude f e) : (normalizationGcd f).divisions ≤ 2 * (e + 1) + 1 := by
  have hd := GodMoveEuclideanBitIterations.gcd_divisions_le
    f.numerator.natAbs f.denominator
  have hs := h.raw_sizes.2
  dsimp [normalizationGcd]
  omega

/-- Every actual gcd division uses positive divisors and the same bounded width. -/
theorem Magnitude.normalizationGcd_input_sizes {f : RawFraction} {e : ℕ}
    (h : Magnitude f e) (p : ℕ × ℕ)
    (hp : p ∈ GodMoveEuclideanBitIterations.divisionInputs
      (2 * f.denominator.size + 1) f.numerator.natAbs f.denominator) :
    p.1.size ≤ e + 1 ∧ p.2.size ≤ e + 1 ∧ 0 < p.2 := by
  have hb := GodMoveEuclideanBitIterations.divisionInputs_bounds
    _ _ _ (2 ^ e) h.1 h.2 p hp
  exact ⟨size_le_of_magnitude hb.1, size_le_of_magnitude hb.2.1, hb.2.2⟩

end GodMoveRationalPrimitiveBounds

#print axioms GodMoveRationalPrimitiveBounds.normalize_rawAdd
#print axioms GodMoveRationalPrimitiveBounds.normalize_rawDiv
#print axioms GodMoveRationalPrimitiveBounds.cross_products_bound
#print axioms GodMoveRationalPrimitiveBounds.rawAdd_magnitude
#print axioms GodMoveRationalPrimitiveBounds.rawSub_magnitude
#print axioms GodMoveRationalPrimitiveBounds.rawMul_magnitude
#print axioms GodMoveRationalPrimitiveBounds.rawDiv_magnitude
#print axioms GodMoveRationalPrimitiveBounds.cancellation_remainders_zero
#print axioms GodMoveRationalPrimitiveBounds.normalization_non_growth
#print axioms GodMoveRationalPrimitiveBounds.Magnitude.cancellation_sizes
#print axioms GodMoveRationalPrimitiveBounds.normalizationGcd_correct
#print axioms GodMoveRationalPrimitiveBounds.Magnitude.normalizationGcd_divisions
#print axioms GodMoveRationalPrimitiveBounds.Magnitude.normalizationGcd_input_sizes
