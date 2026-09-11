import GodMoveGramPrecision

/-!
# Canonical rational precision under finite arithmetic

These bounds concern the numerator and positive denominator of the reduced
rational result. Common-denominator certificates bound complete sums directly;
the generic sum bound grows linearly in the number of summands at the bit level.
Neither theorem asserts a cost model for Lean's integer arithmetic or a Turing
machine implementation. Bounds for stored algorithm rows must be supplied by
their proved algebraic formulas, rather than recursively assumed from this file.
-/

namespace GodMoveRationalPrecisionArithmetic

open scoped BigOperators

/-- Separate bounds on the canonical numerator magnitude and denominator. -/
def Bound (q : ℚ) (N D : ℕ) : Prop := q.num.natAbs ≤ N ∧ q.den ≤ D

theorem Bound.mono {q : ℚ} {N D N' D' : ℕ} (h : Bound q N D)
    (hN : N ≤ N') (hD : D ≤ D') : Bound q N' D' :=
  ⟨h.1.trans hN, h.2.trans hD⟩

theorem ratio_bound (a d : ℤ) (hd : d ≠ 0) :
    Bound ((a : ℚ) / d) a.natAbs d.natAbs :=
  GodMoveGramPrecision.rat_ratio_num_den_le a d hd

theorem Bound.neg {q : ℚ} {N D : ℕ} (h : Bound q N D) : Bound (-q) N D := by
  simpa [Bound] using h

theorem Bound.add {q r : ℚ} {N D N' D' : ℕ}
    (hq : Bound q N D) (hr : Bound r N' D') :
    Bound (q + r) (N * D' + N' * D) (D * D') := by
  have hd : (q.den : ℤ) * r.den ≠ 0 := by positivity
  have h := ratio_bound (q.num * r.den + q.den * r.num) ((q.den : ℤ) * r.den) hd
  rw [← Rat.divInt_eq_div, ← Rat.add_num_den] at h
  apply h.mono
  · calc
      _ ≤ (q.num * r.den).natAbs + ((q.den : ℤ) * r.num).natAbs :=
        Int.natAbs_add_le _ _
      _ ≤ N * D' + N' * D := by
        simp only [Int.natAbs_mul, Int.natAbs_natCast]
        nlinarith [Nat.mul_le_mul hq.1 hr.2, Nat.mul_le_mul hq.2 hr.1]
  · simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Nat.mul_le_mul hq.2 hr.2

theorem Bound.sub {q r : ℚ} {N D N' D' : ℕ}
    (hq : Bound q N D) (hr : Bound r N' D') :
    Bound (q - r) (N * D' + N' * D) (D * D') := by
  simpa only [sub_eq_add_neg] using hq.add hr.neg

theorem Bound.mul {q r : ℚ} {N D N' D' : ℕ}
    (hq : Bound q N D) (hr : Bound r N' D') :
    Bound (q * r) (N * N') (D * D') := by
  have hd : (q.den : ℤ) * r.den ≠ 0 := by positivity
  have h := ratio_bound (q.num * r.num) ((q.den : ℤ) * r.den) hd
  have he : ((q.num * r.num : ℤ) : ℚ) / (((q.den : ℤ) * r.den : ℤ) : ℚ) = q * r := by
    push_cast
    rw [← div_mul_div_comm, Rat.num_div_den, Rat.num_div_den]
  rw [he] at h
  apply h.mono
  · simpa only [Int.natAbs_mul] using Nat.mul_le_mul hq.1 hr.1
  · simpa only [Int.natAbs_mul, Int.natAbs_natCast] using Nat.mul_le_mul hq.2 hr.2

theorem Bound.inv {q : ℚ} {N D : ℕ} (h : Bound q N D) :
    Bound q⁻¹ D (max 1 N) := by
  by_cases hq : q = 0
  · subst q
    simp [Bound]
  · have hn : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
    constructor
    · simpa [Rat.num_inv, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hn] using h.2
    · rw [Rat.den_inv_of_ne_zero hq]
      exact h.1.trans (le_max_right _ _)

theorem Bound.div {q r : ℚ} {N D N' D' : ℕ}
    (hq : Bound q N D) (hr : Bound r N' D') :
    Bound (q / r) (N * D') (D * max 1 N') := by
  simpa only [div_eq_mul_inv] using hq.mul hr.inv

theorem Bound.div_of_ne_zero {q r : ℚ} {N D N' D' : ℕ}
    (hq : Bound q N D) (hr : Bound r N' D') (h : r ≠ 0) :
    Bound (q / r) (N * D') (D * N') := by
  have hn : 1 ≤ N' := by
    have hne : r.num.natAbs ≠ 0 := by simpa using Rat.num_ne_zero.mpr h
    have hbound := hr.1
    omega
  simpa only [max_eq_right hn] using hq.div hr

/-- Every intermediate finite partial sum is covered by taking its index set. -/
theorem sum_commonDenominator_bound {ι : Type*} (s : Finset ι)
    (a : ι → ℤ) (d : ℤ) (hd : d ≠ 0) (N : ℕ)
    (ha : ∀ i ∈ s, (a i).natAbs ≤ N) :
    Bound (∑ i ∈ s, (a i : ℚ) / d) (s.card * N) d.natAbs := by
  have he : (∑ i ∈ s, (a i : ℚ) / d) = ((∑ i ∈ s, a i : ℤ) : ℚ) / d := by
    simp [Finset.sum_div]
  rw [he]
  apply (ratio_bound _ d hd).mono ?_ le_rfl
  calc
    (∑ i ∈ s, a i).natAbs ≤ ∑ i ∈ s, (a i).natAbs := by
      have hsum := Finset.abs_sum_le_sum_abs a s
      simp only [← Int.natCast_natAbs] at hsum
      exact_mod_cast hsum
    _ ≤ s.card * N := by simpa using Finset.sum_le_sum ha

theorem dot_commonDenominator_bound {ι : Type*} (s : Finset ι)
    (a b : ι → ℤ) (d e : ℤ) (hd : d ≠ 0) (he : e ≠ 0) (N M : ℕ)
    (ha : ∀ i ∈ s, (a i).natAbs ≤ N) (hb : ∀ i ∈ s, (b i).natAbs ≤ M) :
    Bound (∑ i ∈ s, ((a i : ℚ) / d) * ((b i : ℚ) / e))
      (s.card * (N * M)) (d.natAbs * e.natAbs) := by
  have h := sum_commonDenominator_bound s (fun i => a i * b i) (d * e)
    (mul_ne_zero hd he) (N * M) (fun i hi => by
      simpa only [Int.natAbs_mul] using Nat.mul_le_mul (ha i hi) (hb i hi))
  simpa only [Int.cast_mul, div_mul_div_comm, Int.natAbs_mul] using h

/-- A uniform height bound gives only linear growth of bit precision in the
number of summands, even without a shared denominator. -/
theorem sum_bound {ι : Type*} (s : Finset ι) (f : ι → ℚ) (B : ℕ)
    (hf : ∀ i ∈ s, Bound (f i) B B) :
    Bound (∑ i ∈ s, f i) (s.card * B ^ s.card) (B ^ s.card) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Bound]
  | @insert a s ha ih =>
      have h := (hf a (by simp)).add (ih (fun i hi => hf i (by simp [hi])))
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      convert h using 1 <;> ring

/-- `b` bounds magnitude exponents; each canonical integer then needs at most
`b+1` magnitude bits, with the numerator sign accounted for separately. -/
def BitBound (q : ℚ) (b : ℕ) : Prop := Bound q (2 ^ b) (2 ^ b)

theorem BitBound.mono {q : ℚ} {b c : ℕ} (h : BitBound q b) (hbc : b ≤ c) :
    BitBound q c := Bound.mono h (Nat.pow_le_pow_right (by decide) hbc)
      (Nat.pow_le_pow_right (by decide) hbc)

theorem BitBound.neg {q : ℚ} {b : ℕ} (h : BitBound q b) : BitBound (-q) b :=
  Bound.neg h

theorem BitBound.canonical_sizes {q : ℚ} {b : ℕ} (h : BitBound q b) :
    q.num.natAbs.size ≤ b + 1 ∧ q.den.size ≤ b + 1 := by
  constructor <;> apply Nat.size_le.mpr
  · exact h.1.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self b))
  · exact h.2.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self b))

theorem BitBound.add {q r : ℚ} {b c : ℕ} (hq : BitBound q b) (hr : BitBound r c) :
    BitBound (q + r) (b + c + 1) := by
  apply Bound.mono (Bound.add hq hr)
  · simp only [pow_add, pow_one]
    nlinarith
  · simp only [pow_add, pow_one]
    omega

theorem BitBound.sub {q r : ℚ} {b c : ℕ} (hq : BitBound q b) (hr : BitBound r c) :
    BitBound (q - r) (b + c + 1) := by
  simpa only [sub_eq_add_neg] using hq.add hr.neg

theorem BitBound.mul {q r : ℚ} {b c : ℕ} (hq : BitBound q b) (hr : BitBound r c) :
    BitBound (q * r) (b + c) := by
  simpa only [BitBound, pow_add] using (Bound.mul hq hr)

theorem BitBound.div {q r : ℚ} {b c : ℕ} (hq : BitBound q b) (hr : BitBound r c) :
    BitBound (q / r) (b + c) := by
  have hpos : 1 ≤ 2 ^ c := Nat.one_le_pow _ _ (by decide)
  simpa only [BitBound, pow_add, max_eq_right hpos] using (Bound.div hq hr)

theorem sum_bitBound {ι : Type*} (s : Finset ι) (f : ι → ℚ) (b : ℕ)
    (hf : ∀ i ∈ s, BitBound (f i) b) :
    BitBound (∑ i ∈ s, f i) ((b + 1) * s.card) := by
  have h := sum_bound s f (2 ^ b) hf
  apply h.mono
  · calc
      s.card * (2 ^ b) ^ s.card ≤ 2 ^ s.card * (2 ^ b) ^ s.card :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.lt_two_pow_self (n := s.card)))
      _ = 2 ^ ((b + 1) * s.card) := by rw [← pow_mul, ← pow_add]; congr 1; ring
  · rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by nlinarith)

theorem dot_bitBound {ι : Type*} (s : Finset ι) (f g : ι → ℚ) (b c : ℕ)
    (hf : ∀ i ∈ s, BitBound (f i) b) (hg : ∀ i ∈ s, BitBound (g i) c) :
    BitBound (∑ i ∈ s, f i * g i) ((b + c + 1) * s.card) :=
  sum_bitBound s _ (b + c) (fun i hi => (hf i hi).mul (hg i hi))

theorem list_sum_bound {ι : Type*} (xs : List ι) (f : ι → ℚ) (B : ℕ)
    (hf : ∀ i ∈ xs, Bound (f i) B B) :
    Bound (xs.map f).sum (xs.length * B ^ xs.length) (B ^ xs.length) := by
  induction xs with
  | nil => simp [Bound]
  | cons a xs ih =>
      have h := (hf a (by simp)).add (ih (fun i hi => hf i (by simp [hi])))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      convert h using 1 <;> ring

/-- No distinctness assumption is needed for the list or its prefixes. -/
theorem list_sum_bitBound {ι : Type*} (xs : List ι) (f : ι → ℚ) (b : ℕ)
    (hf : ∀ i ∈ xs, BitBound (f i) b) :
    BitBound (xs.map f).sum ((b + 1) * xs.length) := by
  have h := list_sum_bound xs f (2 ^ b) hf
  apply h.mono
  · calc
      xs.length * (2 ^ b) ^ xs.length ≤ 2 ^ xs.length * (2 ^ b) ^ xs.length :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.lt_two_pow_self (n := xs.length)))
      _ = 2 ^ ((b + 1) * xs.length) := by rw [← pow_mul, ← pow_add]; congr 1; ring
  · rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by nlinarith)

theorem list_dot_bitBound {ι : Type*} (xs : List ι) (f g : ι → ℚ) (b c : ℕ)
    (hf : ∀ i ∈ xs, BitBound (f i) b) (hg : ∀ i ∈ xs, BitBound (g i) c) :
    BitBound (xs.map (fun i => f i * g i)).sum ((b + c + 1) * xs.length) :=
  list_sum_bitBound xs _ (b + c) (fun i hi => (hf i hi).mul (hg i hi))

theorem list_partialSum_bitBound {ι : Type*} (xs : List ι) (f : ι → ℚ)
    (b k : ℕ) (hf : ∀ i ∈ xs, BitBound (f i) b) :
    BitBound ((xs.take k).map f).sum ((b + 1) * min k xs.length) := by
  simpa only [List.length_take] using
    list_sum_bitBound (xs.take k) f b (fun i hi => hf i (List.mem_of_mem_take hi))

theorem list_partialDot_bitBound {ι : Type*} (xs : List ι) (f g : ι → ℚ)
    (b c k : ℕ) (hf : ∀ i ∈ xs, BitBound (f i) b)
    (hg : ∀ i ∈ xs, BitBound (g i) c) :
    BitBound ((xs.take k).map (fun i => f i * g i)).sum
      ((b + c + 1) * min k xs.length) := by
  simpa only [List.length_take] using
    list_dot_bitBound (xs.take k) f g b c
      (fun i hi => hf i (List.mem_of_mem_take hi))
      (fun i hi => hg i (List.mem_of_mem_take hi))

end GodMoveRationalPrecisionArithmetic

#print axioms GodMoveRationalPrecisionArithmetic.Bound.add
#print axioms GodMoveRationalPrecisionArithmetic.Bound.sub
#print axioms GodMoveRationalPrecisionArithmetic.Bound.mul
#print axioms GodMoveRationalPrecisionArithmetic.Bound.div
#print axioms GodMoveRationalPrecisionArithmetic.sum_commonDenominator_bound
#print axioms GodMoveRationalPrecisionArithmetic.dot_commonDenominator_bound
#print axioms GodMoveRationalPrecisionArithmetic.sum_bound
#print axioms GodMoveRationalPrecisionArithmetic.BitBound.canonical_sizes
#print axioms GodMoveRationalPrecisionArithmetic.sum_bitBound
#print axioms GodMoveRationalPrecisionArithmetic.dot_bitBound
#print axioms GodMoveRationalPrecisionArithmetic.list_partialSum_bitBound
#print axioms GodMoveRationalPrecisionArithmetic.list_partialDot_bitBound
