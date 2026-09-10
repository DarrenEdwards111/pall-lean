import GodMoveNumericCounterexample

/-!
# Clearing rational wire coefficients with an explicit precision bound

The product of the supplied rational denominators is a positive common
denominator. Multiplying by it turns every Boolean wire relation into an
exact integer relation. The integer weights are computed using products with
one denominator omitted, so no coefficient search or identity oracle appears.

If each supplied numerator magnitude and denominator is at most `2^b`, the
common denominator is at most `2^(s*b)` and every cleared weight magnitude is
at most `2^((s+1)*b)`. This bounds the precision increase in this operation.
It does not prove a precision bound for the preceding row-basis algorithm.
-/

namespace GodMoveRationalClearing

open GodMoveBooleanInterpolation GodMoveRowSpanSeparation GodMoveBooleanWireTable
open scoped BigOperators

def commonDen {s : ℕ} (q : Fin s → ℚ) : ℕ := ∏ i, (q i).den

def otherDen {s : ℕ} (q : Fin s → ℚ) (i : Fin s) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, (q j).den

def clearedWeights {s : ℕ} (q : Fin s → ℚ) (i : Fin s) : ℤ :=
  (q i).num * (otherDen q i : ℤ)

theorem commonDen_pos {s : ℕ} (q : Fin s → ℚ) : 0 < commonDen q :=
  Finset.prod_pos (fun i _ => (q i).den_pos)

theorem commonDen_factor {s : ℕ} (q : Fin s → ℚ) (i : Fin s) :
    commonDen q = (q i).den * otherDen q i :=
  (Finset.mul_prod_erase Finset.univ (fun j => (q j).den) (Finset.mem_univ i)).symm

theorem commonDen_mul_coeff {s : ℕ} (q : Fin s → ℚ) (i : Fin s) :
    (commonDen q : ℚ) * q i = (clearedWeights q i : ℚ) := by
  rw [commonDen_factor]
  simp only [Nat.cast_mul, clearedWeights, Int.cast_mul, Int.cast_natCast]
  calc
    _ = ((q i).den : ℚ) * q i * (otherDen q i : ℚ) := by ring
    _ = _ := by rw [Rat.den_mul_eq_num]

def rationalValue {s : ℕ} (q : Fin s → ℚ) (bits : Fin s → Bool) : ℚ :=
  ∑ i, if bits i then q i else 0

def integerValue {s : ℕ} (w : Fin s → ℤ) (bits : Fin s → Bool) : ℤ :=
  ∑ i, if bits i then w i else 0

/-- Equality is derived from rational denominator arithmetic, including
negative weights and cancellations. -/
theorem clear_value {s : ℕ} (q : Fin s → ℚ) (bits : Fin s → Bool) :
    (commonDen q : ℚ) * rationalValue q bits =
      (integerValue (clearedWeights q) bits : ℚ) := by
  rw [rationalValue, integerValue, Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases bits i <;> simp [commonDen_mul_coeff]

theorem rationalValue_zero_iff {s : ℕ} (q : Fin s → ℚ) (bits : Fin s → Bool) :
    rationalValue q bits = 0 ↔ integerValue (clearedWeights q) bits = 0 := by
  have hD : (commonDen q : ℚ) ≠ 0 := by exact_mod_cast (commonDen_pos q).ne'
  have h : (integerValue (clearedWeights q) bits : ℚ) = 0 ↔ rationalValue q bits = 0 := by
    rw [← clear_value]
    simp [hD]
  simpa only [Int.cast_eq_zero] using h.symm

theorem rationalValue_eq_functional {s : ℕ} (q : Fin s → ℚ) (bits : Fin s → Bool) :
    rationalValue q bits = coefficientFunctional q (fun i => bit (bits i)) := by
  rw [rationalValue, coefficientFunctional_apply]
  apply Finset.sum_congr rfl
  intro i _
  cases bits i <;> simp [bit]

/-- A supplied numerator/denominator precision budget, not a bound inferred
from the number of rows or gates. -/
def CoeffPrecision {s : ℕ} (q : Fin s → ℚ) (b : ℕ) : Prop :=
  ∀ i, (q i).num.natAbs ≤ 2 ^ b ∧ (q i).den ≤ 2 ^ b

theorem commonDen_le {s : ℕ} (q : Fin s → ℚ) (b : ℕ) (hb : CoeffPrecision q b) :
    commonDen q ≤ 2 ^ (s * b) := by
  calc
    _ ≤ ∏ _i : Fin s, (2 ^ b : ℕ) := Finset.prod_le_prod' (fun i _ => (hb i).2)
    _ = _ := by simp [← pow_mul, Nat.mul_comm]

theorem otherDen_le_commonDen {s : ℕ} (q : Fin s → ℚ) (i : Fin s) :
    otherDen q i ≤ commonDen q := by
  have hd := (q i).den_pos
  rw [commonDen_factor q i]
  nlinarith

theorem clearedWeights_natAbs_le {s : ℕ} (q : Fin s → ℚ) (b : ℕ)
    (hb : CoeffPrecision q b) (i : Fin s) :
    (clearedWeights q i).natAbs ≤ 2 ^ ((s + 1) * b) := by
  simp only [clearedWeights, Int.natAbs_mul, Int.natAbs_natCast]
  calc
    _ ≤ 2 ^ b * 2 ^ (s * b) := Nat.mul_le_mul (hb i).1
      ((otherDen_le_commonDen q i).trans (commonDen_le q b hb))
    _ = _ := by rw [← pow_add]; congr 1; ring

/-- One padding bit gives a strict bound suitable for fixed-width unsigned
magnitudes. This says nothing about the time to generate the original `q`. -/
theorem clearedWeights_fit {s : ℕ} (q : Fin s → ℚ) (b : ℕ)
    (hb : CoeffPrecision q b) (i : Fin s) :
    (clearedWeights q i).natAbs < 2 ^ ((s + 1) * b + 1) := by
  have h := clearedWeights_natAbs_le q b hb i
  have hp : 0 < (2 : ℕ) ^ ((s + 1) * b) := by positivity
  rw [pow_succ]
  omega

end GodMoveRationalClearing

#print axioms GodMoveRationalClearing.commonDen_pos
#print axioms GodMoveRationalClearing.commonDen_mul_coeff
#print axioms GodMoveRationalClearing.clear_value
#print axioms GodMoveRationalClearing.rationalValue_zero_iff
#print axioms GodMoveRationalClearing.rationalValue_eq_functional
#print axioms GodMoveRationalClearing.commonDen_le
#print axioms GodMoveRationalClearing.clearedWeights_natAbs_le
#print axioms GodMoveRationalClearing.clearedWeights_fit
