import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingShellRatio

/-!
# Linear corrected switching gap

The shell-ratio estimate is summed here for the scaling `n=1000r`, `K=20r`, canonical threshold
`10r`, and saving `9r`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingLinearGap

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellRatio
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermFamily
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellBuckets
open PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout

/-- The number of possible depth shells is absorbed by five exponent bits per scale unit. -/
theorem shell_count_le_pow (r : ℕ) : 20 * r + 1 ≤ 2 ^ (5 * r) := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      calc
        20 * (r + 1) + 1 ≤ 32 * (20 * r + 1) := by omega
        _ ≤ 32 * 2 ^ (5 * r) := Nat.mul_le_mul_left 32 ih
        _ = 2 ^ (5 * (r + 1)) := by
          rw [show 5 * (r + 1) = 5 * r + 5 by ring, pow_add]
          norm_num
          ring

/-- The exponential part of the coarse geometric domination fits the denominator. -/
theorem amplified_exponential_budget (r : ℕ) (hr : 0 < r) :
    2 ^ (14 * r + 1) * 8 ^ (10 * r) ≤ 49 ^ (10 * r) := by
  have htwo : 2 ≤ 2 ^ r := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ r)
  have hbase : 2 ^ 45 ≤ 49 ^ 10 := by norm_num
  calc
    2 ^ (14 * r + 1) * 8 ^ (10 * r)
        = 2 * (2 ^ 44) ^ r := by
          calc
            2 ^ (14 * r + 1) * 8 ^ (10 * r)
                = 2 * (2 ^ 14) ^ r * (8 ^ 10) ^ r := by
                  rw [pow_add, pow_mul, pow_mul]
                  ring
            _ = 2 * ((2 ^ 14) * (8 ^ 10)) ^ r := by rw [mul_assoc, ← mul_pow]
            _ = 2 * (2 ^ 44) ^ r := by norm_num
    _ ≤ 2 ^ r * (2 ^ 44) ^ r := Nat.mul_le_mul_right _ htwo
    _ = (2 ^ 45) ^ r := by rw [← mul_pow]; ring
    _ ≤ (49 ^ 10) ^ r := Nat.pow_le_pow_left hbase r
    _ = 49 ^ (10 * r) := by rw [pow_mul]

/-- The coarse first-term domination already proves the full rational tail budget. -/
theorem amplified_geometric_budget (r : ℕ) (hr : 0 < r) :
    (2 : ℚ) ^ (9 * r + 1) *
        (∑ t ∈ Finset.Icc (10 * r) (20 * r), ((8 : ℚ) / 49) ^ t) ≤ 1 := by
  have hbase0 : (0 : ℚ) ≤ (8 : ℚ) / 49 := by positivity
  have hbase1 : (8 : ℚ) / 49 ≤ 1 := by norm_num
  have hterm : ∀ t ∈ Finset.Icc (10 * r) (20 * r),
      ((8 : ℚ) / 49) ^ t ≤ ((8 : ℚ) / 49) ^ (10 * r) := by
    intro t ht
    exact pow_le_pow_of_le_one hbase0 hbase1 (Finset.mem_Icc.mp ht).1
  have hsum := Finset.sum_le_sum hterm
  have hcard : (Finset.Icc (10 * r) (20 * r)).card ≤ 20 * r + 1 := by
    simp
  calc
    (2 : ℚ) ^ (9 * r + 1) *
        (∑ t ∈ Finset.Icc (10 * r) (20 * r), ((8 : ℚ) / 49) ^ t)
      ≤ 2 ^ (9 * r + 1) *
          ((Finset.Icc (10 * r) (20 * r)).card * ((8 : ℚ) / 49) ^ (10 * r)) := by
            gcongr
            simpa using hsum
    _ ≤ 2 ^ (9 * r + 1) *
          ((2 ^ (5 * r) : ℕ) * ((8 : ℚ) / 49) ^ (10 * r)) := by
            gcongr
            exact_mod_cast hcard.trans (shell_count_le_pow r)
    _ ≤ 1 := by
      rw [div_pow]
      rw [show (2 : ℚ) ^ (9 * r + 1) *
          ((2 ^ (5 * r) : ℕ) * (8 ^ (10 * r) / 49 ^ (10 * r))) =
          (2 ^ (9 * r + 1) * (2 ^ (5 * r) : ℕ) * 8 ^ (10 * r)) /
            49 ^ (10 * r) by field_simp]
      apply (div_le_iff₀ (by positivity : (0 : ℚ) < (49 : ℚ) ^ (10 * r))).2
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [← pow_add]
      simpa [show 9 * r + 1 + 5 * r = 14 * r + 1 by ring] using
        (show ((2 ^ (14 * r + 1) * 8 ^ (10 * r) : ℕ) : ℚ) ≤ 49 ^ (10 * r) by
          exact_mod_cast amplified_exponential_budget r hr)

/-- The rational geometric estimate converted back to the exact natural shell budget. -/
theorem linearGap_shellBudget (r : ℕ) (hr : 0 < r) :
    (∑ t ∈ Finset.Icc (10 * r) (20 * r),
        (1000 * r).choose (20 * r - t) *
          2 ^ (1000 * r - (20 * r - t)) * (2 * 2 * 1) ^ t)
        * 2 ^ (9 * r + 1)
      ≤ (1000 * r).choose (20 * r) * 2 ^ (1000 * r - 20 * r) := by
  have hK : 20 * r ≤ 1000 * r := by omega
  have hfull : (0 : ℚ) < (1000 * r).choose (20 * r) := by
    exact_mod_cast Nat.choose_pos hK
  have hterm : ∀ t ∈ Finset.Icc (10 * r) (20 * r),
      (((1000 * r).choose (20 * r - t) : ℕ) : ℚ) * 8 ^ t ≤
        ((1000 * r).choose (20 * r) : ℕ) * ((8 : ℚ) / 49) ^ t := by
    intro t ht
    have htK : t ≤ 20 * r := (Finset.mem_Icc.mp ht).2
    have hratio := amplified_choose_shell_ratio r t hr htK
    calc
      (((1000 * r).choose (20 * r - t) : ℕ) : ℚ) * 8 ^ t
          = ((((1000 * r).choose (20 * r - t) : ℚ) /
              (1000 * r).choose (20 * r)) * (1000 * r).choose (20 * r)) * 8 ^ t := by
                field_simp [ne_of_gt hfull]
      _ ≤ ((((1 : ℚ) / 49) ^ t) * (1000 * r).choose (20 * r)) * 8 ^ t := by
            gcongr
      _ = ((1000 * r).choose (20 * r) : ℕ) * ((8 : ℚ) / 49) ^ t := by
            simp_rw [div_pow]
            field_simp [pow_ne_zero]
            ring
  have hsum := Finset.sum_le_sum hterm
  have hgeom := amplified_geometric_budget r hr
  have hnormalized :
      (2 : ℚ) ^ (9 * r + 1) *
          (∑ t ∈ Finset.Icc (10 * r) (20 * r),
            (((1000 * r).choose (20 * r - t) : ℕ) : ℚ) * 8 ^ t)
        ≤ ((1000 * r).choose (20 * r) : ℕ) := by
    calc
      (2 : ℚ) ^ (9 * r + 1) *
          (∑ t ∈ Finset.Icc (10 * r) (20 * r),
            (((1000 * r).choose (20 * r - t) : ℕ) : ℚ) * 8 ^ t)
        ≤ 2 ^ (9 * r + 1) *
            ((1000 * r).choose (20 * r) *
              ∑ t ∈ Finset.Icc (10 * r) (20 * r), ((8 : ℚ) / 49) ^ t) := by
                gcongr
                simpa [Finset.mul_sum] using hsum
      _ = ((1000 * r).choose (20 * r) : ℕ) *
            (2 ^ (9 * r + 1) *
              ∑ t ∈ Finset.Icc (10 * r) (20 * r), ((8 : ℚ) / 49) ^ t) := by ring
      _ ≤ ((1000 * r).choose (20 * r) : ℕ) := by
            nlinarith
  have hnormalizedNat :
      2 ^ (9 * r + 1) *
          (∑ t ∈ Finset.Icc (10 * r) (20 * r),
            (1000 * r).choose (20 * r - t) * 8 ^ t)
        ≤ (1000 * r).choose (20 * r) := by
    exact_mod_cast hnormalized
  have hfactor :
      (∑ t ∈ Finset.Icc (10 * r) (20 * r),
        (1000 * r).choose (20 * r - t) *
          2 ^ (1000 * r - (20 * r - t)) * 4 ^ t)
        = 2 ^ (1000 * r - 20 * r) *
          (∑ t ∈ Finset.Icc (10 * r) (20 * r),
            (1000 * r).choose (20 * r - t) * 8 ^ t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have htK : t ≤ 20 * r := (Finset.mem_Icc.mp ht).2
    rw [show 1000 * r - (20 * r - t) = (1000 * r - 20 * r) + t by omega,
      pow_add]
    calc
      (1000 * r).choose (20 * r - t) *
          (2 ^ (1000 * r - 20 * r) * 2 ^ t) * 4 ^ t
        = 2 ^ (1000 * r - 20 * r) *
            ((1000 * r).choose (20 * r - t) * (2 ^ t * 4 ^ t)) := by ring
      _ = 2 ^ (1000 * r - 20 * r) *
            ((1000 * r).choose (20 * r - t) * 8 ^ t) := by
              rw [← mul_pow]
              norm_num
  rw [hfactor]
  calc
    (2 ^ (1000 * r - 20 * r) *
        ∑ t ∈ Finset.Icc (10 * r) (20 * r),
          (1000 * r).choose (20 * r - t) * 8 ^ t) * 2 ^ (9 * r + 1)
      = 2 ^ (1000 * r - 20 * r) *
          (2 ^ (9 * r + 1) *
            ∑ t ∈ Finset.Icc (10 * r) (20 * r),
              (1000 * r).choose (20 * r - t) * 8 ^ t) := by ring
    _ ≤ 2 ^ (1000 * r - 20 * r) * (1000 * r).choose (20 * r) :=
      Nat.mul_le_mul_left _ hnormalizedNat
    _ = (1000 * r).choose (20 * r) * 2 ^ (1000 * r - 20 * r) := by ring

/-- **Uniform linear exponent gap for every positive scale.** -/
theorem linearGap_selectedBucket_activeGap
    (r : ℕ) [NeZero r] (cs : List (Clause (1000 * r)))
    (hw : ∀ T ∈ cs, T.lits.length ≤ 2) (hm : cs.length ≤ 1) :
    ∃ i : Fin ((1000 * r).choose (20 * r)),
      goodBadWork (1000 * r) (1000 * r - 20 * r) (2 ^ (1000 * r - 20 * r))
        (concreteBadCount (K := 20 * r) (boundedTermBad cs (20 * r) (10 * r)) i)
        (10 * r - 1) ≤ 2 ^ (1000 * r - 9 * r) := by
  apply boundedTerm_selectedBucket_activeGap cs hw hm
  · omega
  · have := NeZero.pos r; omega
  · have := NeZero.pos r; omega
  · have := NeZero.pos r; omega
  · exact linearGap_shellBudget r (NeZero.pos r)

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingLinearGap

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingLinearGap.amplified_geometric_budget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingLinearGap.linearGap_shellBudget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingLinearGap.linearGap_selectedBucket_activeGap
