import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0GoodBadSwitchingCashout

/-!
# Switching-tail bridge: dyadic probability bound to an integer bad-leaf count

The good/bad SAT cash-out needs the integer estimate

`badCount ≤ 2^(q-saving-1)`.

A switching theorem naturally supplies the equivalent dyadic tail statement

`badCount / 2^q ≤ 2^(-(saving+1))`.

To avoid division and rounding ambiguity, this file uses its exact cross-multiplied natural-number
form:

`badCount * 2^(saving+1) ≤ 2^q`.

When `saving+1 ≤ q`, cancellation yields precisely the exceptional-count bound required by the
SAT theorem.  The final theorem composes this bridge with the full good/bad work calculation.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingTailIntegerBridge

open PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout

/-- Factor the total restriction count into exceptional-saving and tail-denominator powers. -/
theorem pow_factor_tail (q saving : ℕ) (h : saving + 1 ≤ q) :
    2 ^ q = 2 ^ (q - saving - 1) * 2 ^ (saving + 1) := by
  rw [← Nat.pow_add]
  congr 1
  omega

/-- **Dyadic tail to integer count.**  This is the exact discrete form of converting a switching
failure probability at most `2^(-(saving+1))` into a count of bad restrictions. -/
theorem badCount_le_of_dyadic_tail (q saving badCount : ℕ)
    (hsq : saving + 1 ≤ q)
    (htail : badCount * 2 ^ (saving + 1) ≤ 2 ^ q) :
    badCount ≤ 2 ^ (q - saving - 1) := by
  rw [pow_factor_tail q saving hsq] at htail
  exact le_of_mul_le_mul_right htail (by positivity)

/-- Conversely, the integer exceptional-count bound implies the cross-multiplied dyadic tail. -/
theorem dyadic_tail_of_badCount_le (q saving badCount : ℕ)
    (hsq : saving + 1 ≤ q)
    (hbad : badCount ≤ 2 ^ (q - saving - 1)) :
    badCount * 2 ^ (saving + 1) ≤ 2 ^ q := by
  rw [pow_factor_tail q saving hsq]
  exact Nat.mul_le_mul_right _ hbad

/-- The dyadic probability statement and the integer count statement are exactly equivalent. -/
theorem dyadic_tail_iff_badCount_le (q saving badCount : ℕ)
    (hsq : saving + 1 ≤ q) :
    badCount * 2 ^ (saving + 1) ≤ 2 ^ q ↔
      badCount ≤ 2 ^ (q - saving - 1) :=
  ⟨badCount_le_of_dyadic_tail q saving badCount hsq,
    dyadic_tail_of_badCount_le q saving badCount hsq⟩

/-- **End-to-end tail cash-out.**  A dyadic switching-tail bound plus shallow good residuals yields
the active-normalized SAT work bound, with all exceptional leaves brute-forced. -/
theorem switchingTail_to_activeGap
    (N q goodCount badCount residualDepth saving : ℕ)
    (hq : q ≤ N) (hs : saving + 1 ≤ N) (hsq : saving + 1 ≤ q)
    (hleaves : goodCount ≤ 2 ^ q)
    (hdepth : q + residualDepth ≤ N - saving - 1)
    (htail : badCount * 2 ^ (saving + 1) ≤ 2 ^ q) :
    goodBadWork N q goodCount badCount residualDepth ≤ 2 ^ (N - saving) := by
  apply goodBadWork_le_active_gap N q goodCount badCount residualDepth saving
    hq hs hsq hleaves hdepth
  exact badCount_le_of_dyadic_tail q saving badCount hsq htail

/-- Positive saving turns the same tail certificate into strict sub-brute-force work. -/
theorem switchingTail_to_strictSpeedup
    (N q goodCount badCount residualDepth saving : ℕ)
    (hpos : 0 < saving) (hq : q ≤ N) (hs : saving + 1 ≤ N)
    (hsq : saving + 1 ≤ q) (hleaves : goodCount ≤ 2 ^ q)
    (hdepth : q + residualDepth ≤ N - saving - 1)
    (htail : badCount * 2 ^ (saving + 1) ≤ 2 ^ q) :
    goodBadWork N q goodCount badCount residualDepth < 2 ^ N := by
  apply lt_of_le_of_lt
    (switchingTail_to_activeGap N q goodCount badCount residualDepth saving
      hq hs hsq hleaves hdepth htail)
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingTailIntegerBridge

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingTailIntegerBridge.pow_factor_tail
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingTailIntegerBridge.badCount_le_of_dyadic_tail
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingTailIntegerBridge.dyadic_tail_iff_badCount_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingTailIntegerBridge.switchingTail_to_activeGap
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingTailIntegerBridge.switchingTail_to_strictSpeedup
