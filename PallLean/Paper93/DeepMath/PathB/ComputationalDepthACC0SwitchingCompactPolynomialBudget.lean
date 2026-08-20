import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SwitchingCircuitLinearGap

/-!
# Dyadic absorption of the compact term-multiplicity overhead

At scale `r = 2^a q`, the compact label contributes at most `(20r+1)^m`.  The theorem
below turns this polynomial factor into one dyadic bit per unit of `r`, subject only to an
explicit finite inequality in `a` and the fixed term bound `m`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget

/-- Every positive natural is bounded by the corresponding power of two. -/
theorem self_le_two_pow (q : ℕ) : q ≤ 2 ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
      cases q with
      | zero => simp
      | succ q =>
          rw [pow_succ]
          omega

theorem succ_sq_le_four_pow (k : ℕ) : (k + 1) ^ 2 ≤ 4 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc
        (k + 1 + 1) ^ 2 ≤ 4 * (k + 1) ^ 2 := by
          simp only [pow_two]
          nlinarith [Nat.zero_le k]
        _ ≤ 4 * 4 ^ k := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ (k + 1) := by rw [pow_succ]; ring

/-- A compact multiplicity label is absorbed by one dyadic bit per scale unit.

The constant `20` is the upper endpoint of the switching shell.  Writing the scale as
`r = 2^a q` gives `20r+1 ≤ 32·2^a·q`; the three factors cost respectively `5m`,
`am`, and at most `qm` exponent bits. -/
theorem compactPolynomial_le_dyadic (m a q : ℕ) (hq : 0 < q)
    (hbudget : 5 * m + a * m + m ≤ 2 ^ a) :
    (20 * (2 ^ a * q) + 1) ^ m ≤ 2 ^ (2 ^ a * q) := by
  have hbase : 20 * (2 ^ a * q) + 1 ≤ 32 * (2 ^ a * q) := by
    have hpos : 0 < 2 ^ a * q := Nat.mul_pos (pow_pos (by norm_num) _) hq
    omega
  have hqpow : q ^ m ≤ (2 ^ q) ^ m := Nat.pow_le_pow_left (self_le_two_pow q) m
  have hexp : 5 * m + a * m + q * m ≤ 2 ^ a * q := by
    calc
      5 * m + a * m + q * m ≤ (5 * m + a * m + m) * q := by
        have hq1 : 1 ≤ q := hq
        calc
          5 * m + a * m + q * m ≤ (5 * m + a * m) * q + q * m := by
            exact Nat.add_le_add (Nat.le_mul_of_pos_right _ hq) le_rfl
          _ = (5 * m + a * m + m) * q := by ring
      _ ≤ 2 ^ a * q := Nat.mul_le_mul_right q hbudget
  calc
    (20 * (2 ^ a * q) + 1) ^ m ≤ (32 * (2 ^ a * q)) ^ m :=
      Nat.pow_le_pow_left hbase m
    _ = 2 ^ (5 * m) * (2 ^ (a * m) * q ^ m) := by
      rw [mul_pow, mul_pow, show 32 = 2 ^ 5 by norm_num, pow_mul, pow_mul]
    _ ≤ 2 ^ (5 * m) * (2 ^ (a * m) * (2 ^ q) ^ m) := by
      gcongr
    _ = 2 ^ (5 * m + a * m + q * m) := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ (2 ^ a * q) := Nat.pow_le_pow_right (by norm_num) hexp

/-- A fully explicit scale choice, requiring no residual numerical premise. -/
theorem compactPolynomial_explicitScale (m q : ℕ) (hq : 0 < q) :
    (20 * (2 ^ (2 * m + 6) * q) + 1) ^ m ≤
      2 ^ (2 ^ (2 * m + 6) * q) := by
  apply compactPolynomial_le_dyadic m (2 * m + 6) q hq
  have hsq := succ_sq_le_four_pow m
  calc
    5 * m + (2 * m + 6) * m + m ≤ 64 * (m + 1) ^ 2 := by nlinarith
    _ ≤ 64 * 4 ^ m := Nat.mul_le_mul_left 64 hsq
    _ = 2 ^ (2 * m + 6) := by
      rw [show 64 = 2 ^ 6 by norm_num, show 4 ^ m = 2 ^ (2 * m) by
        rw [show 4 = 2 ^ 2 by norm_num, pow_mul]]
      rw [← pow_add]
      congr 1
      omega

end PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget.self_le_two_pow
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget.compactPolynomial_le_dyadic
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0SwitchingCompactPolynomialBudget.compactPolynomial_explicitScale
