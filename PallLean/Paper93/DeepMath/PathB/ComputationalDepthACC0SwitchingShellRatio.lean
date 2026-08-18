import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingBoundedTermFamily

/-!
# Binomial shell ratios for symbolic switching amplification

This file supplies the missing symbolic comparison between a lower fixed-star shell and the full
`K`-star shell.  It is stated over `ℚ`, where the exact adjacent-binomial recurrence can be divided
without introducing natural-number rounding.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellRatio

/-- Exact ratio of adjacent binomial coefficients. -/
theorem choose_adjacent_ratio {n j : ℕ} (hj : j < n) :
    (n.choose j : ℚ) / n.choose (j + 1) = (j + 1 : ℚ) / ((n - j : ℕ) : ℚ) := by
  have hpos : 0 < n.choose (j + 1) := Nat.choose_pos (by omega)
  have hdiff : 0 < n - j := by omega
  field_simp
  exact_mod_cast (Nat.choose_succ_right_eq n j).symm

/-- Moving down `t` binomial shells costs at most the `t`th power of the worst adjacent ratio. -/
theorem choose_shell_ratio {n K t : ℕ} (hK : K ≤ n) (ht : t ≤ K) :
    (n.choose (K - t) : ℚ) / n.choose K
      ≤ ((K : ℚ) / ((n - K + 1 : ℕ) : ℚ)) ^ t := by
  induction t with
  | zero =>
      have hp : (0 : ℚ) < n.choose K := by exact_mod_cast Nat.choose_pos hK
      simp [ne_of_gt hp]
  | succ t ih =>
      have htK : t < K := by omega
      have hjn : K - (t + 1) < n := by omega
      have hKt : K - t ≤ n := by omega
      have hmid : (0 : ℚ) < n.choose (K - t) := by exact_mod_cast Nat.choose_pos hKt
      have hden : (0 : ℚ) < n.choose K := by exact_mod_cast Nat.choose_pos hK
      have hadj := choose_adjacent_ratio (n := n) (j := K - t - 1) hjn
      rw [show K - t - 1 + 1 = K - t by omega] at hadj
      have hcastK : (((K - t - 1 : ℕ) : ℚ) + 1) = ((K - t : ℕ) : ℚ) := by
        exact_mod_cast (show K - t - 1 + 1 = K - t by omega)
      rw [show K - (t + 1) = K - t - 1 by omega]
      rw [show (n.choose (K - t - 1) : ℚ) / n.choose K =
          ((n.choose (K - t - 1) : ℚ) / n.choose (K - t)) *
            ((n.choose (K - t) : ℚ) / n.choose K) by
        field_simp [ne_of_gt hmid, ne_of_gt hden]]
      calc
        ((n.choose (K - t - 1) : ℚ) / n.choose (K - t)) *
              ((n.choose (K - t) : ℚ) / n.choose K)
            = (((K - t : ℕ) : ℚ) / ((n - (K - t - 1) : ℕ) : ℚ)) *
              ((n.choose (K - t) : ℚ) / n.choose K) := by
                rw [hadj, hcastK]
        _ ≤ ((K : ℚ) / ((n - K + 1 : ℕ) : ℚ)) *
              (((K : ℚ) / ((n - K + 1 : ℕ) : ℚ)) ^ t) := by
                apply mul_le_mul
                · apply div_le_div₀
                  · positivity
                  · exact_mod_cast (Nat.sub_le K t)
                  · exact_mod_cast (by omega : 0 < n - K + 1)
                  · exact_mod_cast (by omega : n - K + 1 ≤ n - (K - t - 1))
                · simpa [show K - t - 1 + 1 = K - t by omega] using ih (by omega)
                · positivity
                · positivity
        _ = ((K : ℚ) / ((n - K + 1 : ℕ) : ℚ)) ^ (t + 1) := by ring

/-- At the amplification density `K/n = 1/50`, every downward shell step costs at most `1/49`. -/
theorem amplified_choose_shell_ratio (r t : ℕ) (hr : 0 < r) (ht : t ≤ 20 * r) :
    (((1000 * r).choose (20 * r - t) : ℚ) / (1000 * r).choose (20 * r))
      ≤ ((1 : ℚ) / 49) ^ t := by
  have hK : 20 * r ≤ 1000 * r := by omega
  have hbase := choose_shell_ratio (n := 1000 * r) (K := 20 * r) (t := t) hK ht
  have hratio :
      ((20 * r : ℕ) : ℚ) / (((1000 * r - 20 * r + 1 : ℕ) : ℚ)) ≤ (1 : ℚ) / 49 := by
    rw [show 1000 * r - 20 * r + 1 = 980 * r + 1 by omega]
    apply (div_le_iff₀ (show (0 : ℚ) < ((980 * r + 1 : ℕ) : ℚ) by positivity)).2
    norm_num
    linarith
  exact hbase.trans (pow_le_pow_left₀ (by positivity) hratio t)

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellRatio

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellRatio.choose_adjacent_ratio
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellRatio.choose_shell_ratio
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingShellRatio.amplified_choose_shell_ratio
