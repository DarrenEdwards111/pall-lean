import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BernoulliTail
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Field.GeomSum

/-!
# Tight switching, step 70: the rational `(1+1/k)^k ≤ 4` bound (branch `razborov-recoverRho-wip`)

The second analytic atom the Chernoff bound `h1` needs: a rational ceiling on `(1+1/k)^k` (the quantity that
controls `t^(s-1)` for `t = 1 - 1/s`), without `exp`.  By the binomial theorem `(1+1/k)^k =
∑_{m≤k} C(k,m)/k^m`, each term `C(k,m)/k^m ≤ 1/m!` (Mathlib's `choose_le_pow_div`), and `∑ 1/m! ≤ 4` via the
geometric bound `1/m! ≤ 2·(1/2)^m` (from `2^m ≤ 2·m!`).  So `(1+1/k)^k ≤ ∑_{m≤k} 1/m! ≤ 4`.

* `two_pow_le_two_mul_factorial` — `2^m ≤ 2·m!`.
* `inv_factorial_sum_le_four` — `∑_{m<N} 1/m! ≤ 4`.
* `one_add_inv_pow_le_four` — `(1+1/k)^k ≤ 4`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open Finset

/-- `2^m ≤ 2·m!` for all `m`. -/
theorem two_pow_le_two_mul_factorial (m : ℕ) : 2 ^ m ≤ 2 * m.factorial := by
  induction m with
  | zero => norm_num
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; norm_num [Nat.factorial]
    · calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        _ ≤ 2 * (2 * k.factorial) := by omega
        _ ≤ 2 * ((k + 1) * k.factorial) := by
            apply Nat.mul_le_mul_left
            exact Nat.mul_le_mul_right _ (by omega)
        _ = 2 * (k + 1).factorial := by rw [Nat.factorial_succ]

/-- Each `1/m!` is dominated by the geometric `2·(1/2)^m`. -/
theorem inv_factorial_le_geom (m : ℕ) : (1 : ℚ) / m.factorial ≤ 2 * (1 / 2) ^ m := by
  have hnat := two_pow_le_two_mul_factorial m
  have h2 : (2 : ℚ) ^ m ≤ 2 * (m.factorial : ℚ) := by exact_mod_cast hnat
  have hfpos : (0 : ℚ) < (m.factorial : ℚ) := by exact_mod_cast m.factorial_pos
  have hppos : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
  rw [show (2 : ℚ) * (1 / 2) ^ m = 2 / 2 ^ m by rw [div_pow, one_pow, mul_one_div]]
  rw [le_div_iff₀ hppos, div_mul_eq_mul_div, one_mul, div_le_iff₀ hfpos]
  exact h2

/-- `∑_{m<N} 1/m! ≤ 4`. -/
theorem inv_factorial_sum_le_four (N : ℕ) :
    ∑ m ∈ range N, (1 : ℚ) / m.factorial ≤ 4 := by
  have hgeom : ∑ m ∈ range N, (1 / 2 : ℚ) ^ m ≤ 2 := by
    rw [geom_sum_eq (by norm_num : (1 / 2 : ℚ) ≠ 1)]
    have hpow : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ N := by positivity
    have heq : ((1 / 2 : ℚ) ^ N - 1) / (1 / 2 - 1) = 2 - 2 * (1 / 2) ^ N := by
      field_simp; ring
    rw [heq]; linarith
  calc ∑ m ∈ range N, (1 : ℚ) / m.factorial
      ≤ ∑ m ∈ range N, 2 * (1 / 2 : ℚ) ^ m :=
        Finset.sum_le_sum (fun m _ => inv_factorial_le_geom m)
    _ = 2 * ∑ m ∈ range N, (1 / 2 : ℚ) ^ m := by rw [Finset.mul_sum]
    _ ≤ 2 * 2 := by linarith
    _ = 4 := by norm_num

/-- **The rational `(1+1/k)^k ≤ 4` bound.**  Binomial expansion, each term `≤ 1/m!`, summed by the geometric
ceiling. -/
theorem one_add_inv_pow_le_four (k : ℕ) : (1 + 1 / (k : ℚ)) ^ k ≤ 4 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; norm_num
  · have hkne : (k : ℚ) ≠ 0 := by positivity
    have hbinom : (1 + 1 / (k : ℚ)) ^ k
        = ∑ m ∈ range (k + 1), (1 / (k : ℚ)) ^ m * 1 ^ (k - m) * (k.choose m) := by
      rw [show (1 : ℚ) + 1 / k = 1 / k + 1 by ring]; exact add_pow (1 / (k : ℚ)) 1 k
    rw [hbinom]
    calc ∑ m ∈ range (k + 1), (1 / (k : ℚ)) ^ m * 1 ^ (k - m) * (k.choose m)
        ≤ ∑ m ∈ range (k + 1), (1 : ℚ) / m.factorial := by
          apply Finset.sum_le_sum
          intro m hm
          rw [one_pow, mul_one]
          have hkm : (k : ℚ) ^ m ≠ 0 := by positivity
          have hchoose : (k.choose m : ℚ) ≤ (k : ℚ) ^ m / m.factorial := by
            have := Nat.choose_le_pow_div (α := ℚ) m k
            push_cast at this ⊢
            convert this using 2
          calc (1 / (k : ℚ)) ^ m * (k.choose m)
              ≤ (1 / (k : ℚ)) ^ m * ((k : ℚ) ^ m / m.factorial) := by
                apply mul_le_mul_of_nonneg_left hchoose (by positivity)
            _ = 1 / m.factorial := by rw [div_pow, one_pow]; field_simp
      _ ≤ 4 := inv_factorial_sum_le_four (k + 1)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.one_add_inv_pow_le_four
