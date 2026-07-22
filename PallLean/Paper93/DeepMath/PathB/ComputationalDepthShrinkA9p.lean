import PallLean.Paper93.DeepMath.PathB.ComputationalDepthShrinkA9o

/-!
# Shrinkage brick A9p: exponential beats polynomial

The one non-trivial numeric fact behind the concrete Andreev family's counting
condition:

* **`poly_bound` (proved)** — `32·k⁸ < 2ᵏ` for `k ≥ 255`.

Base case: `255 < 256 = 2⁸`, so `32·255⁸ < 2⁵·2⁶⁴ = 2⁶⁹ ≤ 2²⁵⁵`.  Step:
`(n+1)⁸ ≤ 2·n⁸` for `n ≥ 255` (binomial tail `≤ 255·n⁷ ≤ n⁸`).  Nothing here is
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Khrapchenko

theorem succ_pow8_le (n : ℕ) (hn : 255 ≤ n) : (n + 1) ^ 8 ≤ 2 * n ^ 8 := by
  have hexp : (n + 1) ^ 8 = n ^ 8 + 8 * n ^ 7 + 28 * n ^ 6 + 56 * n ^ 5
      + 70 * n ^ 4 + 56 * n ^ 3 + 28 * n ^ 2 + 8 * n + 1 := by ring
  have h1 : (1 : ℕ) ≤ n := by omega
  have b0 : (1 : ℕ) ≤ n ^ 7 := Nat.one_le_pow _ _ (by omega)
  have b1 : n ≤ n ^ 7 := Nat.le_self_pow (by omega) n
  have b2 : n ^ 2 ≤ n ^ 7 := Nat.pow_le_pow_right h1 (by omega)
  have b3 : n ^ 3 ≤ n ^ 7 := Nat.pow_le_pow_right h1 (by omega)
  have b4 : n ^ 4 ≤ n ^ 7 := Nat.pow_le_pow_right h1 (by omega)
  have b5 : n ^ 5 ≤ n ^ 7 := Nat.pow_le_pow_right h1 (by omega)
  have b6 : n ^ 6 ≤ n ^ 7 := Nat.pow_le_pow_right h1 (by omega)
  have hn8 : 255 * n ^ 7 ≤ n ^ 8 := by
    calc 255 * n ^ 7 ≤ n * n ^ 7 := Nat.mul_le_mul_right _ hn
      _ = n ^ 8 := by ring
  rw [hexp]
  omega

/-- **Exponential beats polynomial (proved)**: `32·k⁸ < 2ᵏ` for `k ≥ 255`. -/
theorem poly_bound (k : ℕ) (hk : 255 ≤ k) : 32 * k ^ 8 < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base =>
    have h1 : (255 : ℕ) ^ 8 < 256 ^ 8 := Nat.pow_lt_pow_left (by norm_num) (by norm_num)
    have h2 : (256 : ℕ) ^ 8 = 2 ^ 64 := by norm_num
    have h3 : 32 * (255 : ℕ) ^ 8 < 32 * 2 ^ 64 := by
      have := h1; rw [h2] at this; omega
    have h4 : 32 * (2 : ℕ) ^ 64 = 2 ^ 69 := by
      rw [show (32 : ℕ) = 2 ^ 5 from rfl, ← pow_add]
    have h5 : (2 : ℕ) ^ 69 ≤ 2 ^ 255 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  | succ n hn ih =>
    have hstep := succ_pow8_le n hn
    calc 32 * (n + 1) ^ 8 ≤ 32 * (2 * n ^ 8) := by
          exact Nat.mul_le_mul_left _ hstep
      _ = 2 * (32 * n ^ 8) := by ring
      _ < 2 * 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

end PallLean.Paper93.DeepMath.PathB.Khrapchenko

#print axioms PallLean.Paper93.DeepMath.PathB.Khrapchenko.poly_bound
