import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingLinearGap

/-!
# Fixed-term corrected switching gap

For every positive fixed term bound `m` and positive scale `r`, take
`n = 1000mr`, `K = 20r`, canonical threshold `10r`, and saving `9r`.
The extra factor `m^t` in the bounded-term witness count is cancelled by the
smaller shell ratio `1/(49m)`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingFixedTermLinearGap

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellRatio
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingBoundedTermFamily
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellBuckets
open PallLean.Paper93.DeepMath.PathB.ACC0GoodBadSwitchingCashout
open PallLean.Paper93.DeepMath.PathB.ACC0SwitchingLinearGap

/-- At density `K/n = 1/(50m)`, a downward shell step costs at most `1/(49m)`. -/
theorem fixedTerm_choose_shell_ratio (m r t : ℕ) (hm : 0 < m) (hr : 0 < r)
    (ht : t ≤ 20 * r) :
    ((((1000 * m * r).choose (20 * r - t) : ℕ) : ℚ) /
        (1000 * m * r).choose (20 * r)) ≤
          ((1 : ℚ) / ((49 * m : ℕ) : ℚ)) ^ t := by
  have hK : 20 * r ≤ 1000 * m * r := by nlinarith
  have hbase := choose_shell_ratio (n := 1000 * m * r) (K := 20 * r) (t := t) hK ht
  have hratio :
      ((20 * r : ℕ) : ℚ) /
          (((1000 * m * r - 20 * r + 1 : ℕ) : ℚ)) ≤
            (1 : ℚ) / ((49 * m : ℕ) : ℚ) := by
    apply (div_le_div_iff₀ (show (0 : ℚ) < ((1000 * m * r - 20 * r + 1 : ℕ) : ℚ) by
      positivity) (show (0 : ℚ) < (49 * m : ℕ) by positivity)).2
    have hrmr : r ≤ m * r := by
      simpa [one_mul] using Nat.mul_le_mul_right r hm
    have hx : 980 * m * r + 20 * r ≤ 1000 * m * r := by nlinarith
    have hsub := Nat.sub_add_cancel hK
    have heq : 20 * r * (49 * m) = 980 * m * r := by ring
    have hnat : 20 * r * (49 * m) ≤ 1000 * m * r - 20 * r + 1 := by omega
    have hrat :
        (((20 * r * (49 * m) : ℕ) : ℚ) ≤
          ((1000 * m * r - 20 * r + 1 : ℕ) : ℚ)) := by exact_mod_cast hnat
    simpa using hrat
  exact hbase.trans (pow_le_pow_left₀ (by positivity) hratio t)

/-- The exact natural-number shell budget for arbitrary positive fixed term bound. -/
theorem fixedTermLinearGap_shellBudget (m r : ℕ) (hm : 0 < m) (hr : 0 < r) :
    (∑ t ∈ Finset.Icc (10 * r) (20 * r),
        (1000 * m * r).choose (20 * r - t) *
          2 ^ (1000 * m * r - (20 * r - t)) * (2 * 2 * m) ^ t)
        * 2 ^ (9 * r + 1)
      ≤ (1000 * m * r).choose (20 * r) * 2 ^ (1000 * m * r - 20 * r) := by
  have hK : 20 * r ≤ 1000 * m * r := by nlinarith
  have hfull : (0 : ℚ) < (1000 * m * r).choose (20 * r) := by
    exact_mod_cast Nat.choose_pos hK
  have hterm : ∀ t ∈ Finset.Icc (10 * r) (20 * r),
      ((((1000 * m * r).choose (20 * r - t) : ℕ) : ℚ) * (8 * m) ^ t) ≤
        ((1000 * m * r).choose (20 * r) : ℕ) * ((8 : ℚ) / 49) ^ t := by
    intro t ht
    have htK : t ≤ 20 * r := (Finset.mem_Icc.mp ht).2
    have hratio := fixedTerm_choose_shell_ratio m r t hm hr htK
    have hratio' :
        (((1000 * m * r).choose (20 * r - t) : ℚ) /
          (1000 * m * r).choose (20 * r)) ≤ ((1 : ℚ) / (49 * m)) ^ t := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hratio
    calc
      (((1000 * m * r).choose (20 * r - t) : ℕ) : ℚ) * (8 * m) ^ t
          = (((((1000 * m * r).choose (20 * r - t) : ℚ) /
              (1000 * m * r).choose (20 * r)) *
                (1000 * m * r).choose (20 * r)) * (8 * m) ^ t) := by
                  field_simp [ne_of_gt hfull]
      _ ≤ ((((1 : ℚ) / (49 * m)) ^ t) *
              (1000 * m * r).choose (20 * r)) * (8 * m) ^ t := by
            gcongr
      _ = ((1000 * m * r).choose (20 * r) : ℕ) * ((8 : ℚ) / 49) ^ t := by
            simp only [mul_pow, div_pow]
            field_simp [show (m : ℚ) ≠ 0 by exact_mod_cast ne_of_gt hm, pow_ne_zero]
            simp
  have hsum := Finset.sum_le_sum hterm
  have hgeom := amplified_geometric_budget r hr
  have hnormalized :
      (2 : ℚ) ^ (9 * r + 1) *
          (∑ t ∈ Finset.Icc (10 * r) (20 * r),
            (((1000 * m * r).choose (20 * r - t) : ℕ) : ℚ) * (8 * m) ^ t)
        ≤ ((1000 * m * r).choose (20 * r) : ℕ) := by
    calc
      _ ≤ 2 ^ (9 * r + 1) *
            ((1000 * m * r).choose (20 * r) *
              ∑ t ∈ Finset.Icc (10 * r) (20 * r), ((8 : ℚ) / 49) ^ t) := by
                gcongr
                simpa [Finset.mul_sum] using hsum
      _ = ((1000 * m * r).choose (20 * r) : ℕ) *
            (2 ^ (9 * r + 1) *
              ∑ t ∈ Finset.Icc (10 * r) (20 * r), ((8 : ℚ) / 49) ^ t) := by ring
      _ ≤ ((1000 * m * r).choose (20 * r) : ℕ) := by nlinarith
  have hnormalizedNat :
      2 ^ (9 * r + 1) *
          (∑ t ∈ Finset.Icc (10 * r) (20 * r),
            (1000 * m * r).choose (20 * r - t) * (8 * m) ^ t)
        ≤ (1000 * m * r).choose (20 * r) := by
    exact_mod_cast hnormalized
  have hfactor :
      (∑ t ∈ Finset.Icc (10 * r) (20 * r),
        (1000 * m * r).choose (20 * r - t) *
          2 ^ (1000 * m * r - (20 * r - t)) * (4 * m) ^ t)
        = 2 ^ (1000 * m * r - 20 * r) *
          (∑ t ∈ Finset.Icc (10 * r) (20 * r),
            (1000 * m * r).choose (20 * r - t) * (8 * m) ^ t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have htK : t ≤ 20 * r := (Finset.mem_Icc.mp ht).2
    rw [show 1000 * m * r - (20 * r - t) =
        (1000 * m * r - 20 * r) + t by omega, pow_add]
    calc
      _ = 2 ^ (1000 * m * r - 20 * r) *
            ((1000 * m * r).choose (20 * r - t) * (2 ^ t * (4 * m) ^ t)) := by ring
      _ = 2 ^ (1000 * m * r - 20 * r) *
            ((1000 * m * r).choose (20 * r - t) * (8 * m) ^ t) := by
              rw [← mul_pow]
              ring
  rw [show 2 * 2 * m = 4 * m by ring, hfactor]
  calc
    _ = 2 ^ (1000 * m * r - 20 * r) *
          (2 ^ (9 * r + 1) *
            ∑ t ∈ Finset.Icc (10 * r) (20 * r),
              (1000 * m * r).choose (20 * r - t) * (8 * m) ^ t) := by ring
    _ ≤ 2 ^ (1000 * m * r - 20 * r) * (1000 * m * r).choose (20 * r) :=
      Nat.mul_le_mul_left _ hnormalizedNat
    _ = (1000 * m * r).choose (20 * r) * 2 ^ (1000 * m * r - 20 * r) := by ring

/-- **Uniform linear exponent gap for every positive fixed term bound.** -/
theorem fixedTermLinearGap_selectedBucket_activeGap
    (m r : ℕ) [NeZero m] [NeZero r] (cs : List (Clause (1000 * m * r)))
    (hw : ∀ T ∈ cs, T.lits.length ≤ 2) (hm : cs.length ≤ m) :
    ∃ i : Fin ((1000 * m * r).choose (20 * r)),
      goodBadWork (1000 * m * r) (1000 * m * r - 20 * r)
        (2 ^ (1000 * m * r - 20 * r))
        (concreteBadCount (K := 20 * r) (boundedTermBad cs (20 * r) (10 * r)) i)
        (10 * r - 1) ≤ 2 ^ (1000 * m * r - 9 * r) := by
  have hmpos := NeZero.pos m
  have hrpos := NeZero.pos r
  have hKn : 20 * r ≤ 1000 * m * r := by nlinarith
  have hsN : 9 * r + 1 ≤ 1000 * m * r := by nlinarith
  have hsaveK : 9 * r + 1 + 20 * r ≤ 1000 * m * r := by nlinarith
  have hworkArithmetic {n r : ℕ} (hr : 0 < r) (h : 20 * r ≤ n) :
      (n - 20 * r) + (10 * r - 1) ≤ n - 9 * r - 1 := by omega
  apply boundedTerm_selectedBucket_activeGap cs hw hm
  · exact hKn
  · omega
  · exact hsN
  · exact hworkArithmetic hrpos hKn
  · exact fixedTermLinearGap_shellBudget m r hmpos hrpos

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingFixedTermLinearGap

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingFixedTermLinearGap.fixedTerm_choose_shell_ratio
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingFixedTermLinearGap.fixedTermLinearGap_shellBudget
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingFixedTermLinearGap.fixedTermLinearGap_selectedBucket_activeGap
