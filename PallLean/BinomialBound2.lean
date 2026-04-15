/-
  BinomialBound2.lean — Prove binomial_lower_bound via pure ℕ Route 2.
-/
import PallLean.BinomialBound

namespace BinomialBound

open Nat

/-! ## Step 1: Power-lifting lemma -/

theorem pow_lift_four (a b k : ℕ) (h4 : a ^ 4 ≥ b) (ha : 1 ≤ a) :
    a ^ k ≥ b ^ (k / 4) := by
  have hk_eq : k = 4 * (k / 4) + k % 4 := (Nat.div_add_mod k 4).symm
  conv_lhs => rw [hk_eq]
  rw [pow_add, pow_mul]
  calc (a ^ 4) ^ (k / 4) * a ^ (k % 4)
      ≥ b ^ (k / 4) * 1 := by
        apply Nat.mul_le_mul
        · exact Nat.pow_le_pow_left h4 _
        · exact Nat.one_le_pow _ _ ha
    _ = b ^ (k / 4) := mul_one _

/-! ## Step 2: 30k ≤ 2^(k/2) for k ≥ 20 -/

private theorem thirty_k_step (k : ℕ) (hk : 12 ≤ k)
    (ih : 30 * k ≤ 2 ^ (k / 2)) :
    30 * (k + 2) ≤ 2 ^ ((k + 2) / 2) := by
  have hkd : k / 2 + 1 ≤ (k + 2) / 2 := by omega
  have h64 : 2 ^ 6 ≤ 2 ^ (k / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 30 * (k + 2) = 30 * k + 60 := by ring
    _ ≤ 2 ^ (k / 2) + 60 := by omega
    _ ≤ 2 ^ (k / 2) + 2 ^ (k / 2) := by omega
    _ = 2 * 2 ^ (k / 2) := by ring
    _ = 2 ^ (k / 2 + 1) := by ring_nf
    _ ≤ 2 ^ ((k + 2) / 2) := Nat.pow_le_pow_right (by norm_num) hkd

theorem thirty_k_le_pow_half (k : ℕ) (hk : 20 ≤ k) : 30 * k ≤ 2 ^ (k / 2) := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk22 : k < 22
    · interval_cases k <;> omega
    · have ih' := ih (k - 2) (by omega) (by omega)
      have hkeq : k = (k - 2) + 2 := by omega
      rw [hkeq]
      exact thirty_k_step (k - 2) (by omega) ih'

/-! ## Step 3: Sandwich and quotient bound -/

theorem quotient_pow4_ge (n : ℕ) (hn : 2 ^ 20 ≤ n) :
    (n / (30 * Nat.log 2 n)) ^ 4 ≥ n := by
  set k := Nat.log 2 n with hk_def
  have hn1 : 1 ≤ n := by omega
  have hk20 : 20 ≤ k := by
    rw [hk_def]
    have h1 : Nat.log 2 (2^20) = 20 := Nat.log_pow (by norm_num) 20
    have h2 : Nat.log 2 (2^20) ≤ Nat.log 2 n := Nat.log_mono (by norm_num) le_rfl hn
    omega
  have hn_ne : n ≠ 0 := by omega
  have h2k_le_n : 2 ^ k ≤ n := hk_def ▸ Nat.pow_log_le_self 2 hn_ne
  have hn_lt : n < 2 ^ (k + 1) := hk_def ▸ Nat.lt_pow_succ_log_self (by norm_num) n
  have h30k := thirty_k_le_pow_half k (by omega)
  have h30k_pos : 0 < 30 * k := by omega
  -- n/(30k) ≥ 2^k/(30k) ≥ 2^(k - k/2)
  have hA : 2 ^ k / (30 * k) ≤ n / (30 * k) := Nat.div_le_div_right h2k_le_n
  have hB : 2 ^ (k - k / 2) ≤ 2 ^ k / (30 * k) := by
    rw [Nat.le_div_iff_mul_le h30k_pos]
    calc 2 ^ (k - k / 2) * (30 * k)
        ≤ 2 ^ (k - k / 2) * 2 ^ (k / 2) := Nat.mul_le_mul_left _ h30k
      _ = 2 ^ k := by rw [← pow_add]; congr 1; omega
  have hquot : 2 ^ (k - k / 2) ≤ n / (30 * k) := le_trans hB hA
  -- (n/(30k))^4 ≥ 2^(4*(k-k/2)) ≥ 2^(2k) ≥ 2^(k+1) > n
  have hpow4 : (n / (30 * k)) ^ 4 ≥ 2 ^ (k + 1) :=
    calc (n / (30 * k)) ^ 4
        ≥ (2 ^ (k - k / 2)) ^ 4 := Nat.pow_le_pow_left hquot 4
      _ = 2 ^ ((k - k / 2) * 4) := by rw [← pow_mul]
      _ = 2 ^ (4 * (k - k / 2)) := by ring_nf
      _ ≥ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≥ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ## Step 4: Combine -/

theorem poly_beats_log :
    ∃ n₀, ∀ n, n ≥ n₀ →
      (n / 30 / Nat.log 2 n) ^ Nat.log 2 n ≥ n ^ (Nat.log 2 n / 4) := by
  use 2 ^ 20
  intro n hn
  rw [Nat.div_div_eq_div_mul]
  set k := Nat.log 2 n
  by_cases hk0 : k = 0
  · simp [hk0]
  · have hq4 := quotient_pow4_ge n hn
    have hk20 : 20 ≤ k := by
      have h1 : Nat.log 2 (2^20) = 20 := Nat.log_pow (by norm_num) 20
      have h2 : Nat.log 2 (2^20) ≤ k := Nat.log_mono (by norm_num) le_rfl hn
      omega
    have hq1 : 1 ≤ n / (30 * k) := by
      apply Nat.div_pos
      · calc 30 * k ≤ 2 ^ (k / 2) := thirty_k_le_pow_half k (by omega)
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ n := Nat.pow_log_le_self 2 (by omega)
      · omega
    exact pow_lift_four _ n k hq4 hq1

theorem binomial_lower_bound' :
    ∃ n₀, ∀ n, n ≥ n₀ →
      Nat.choose (n / 30) (Nat.log 2 n) ≥ n ^ (Nat.log 2 n / 4) := by
  obtain ⟨n₀, hn₀⟩ := poly_beats_log
  use n₀
  intro n hn
  by_cases hk0 : Nat.log 2 n = 0
  · simp [hk0]
  · calc Nat.choose (n / 30) (Nat.log 2 n)
        ≥ (n / 30 / Nat.log 2 n) ^ Nat.log 2 n :=
            choose_ge_div_pow _ _ (Nat.pos_of_ne_zero hk0)
      _ ≥ n ^ (Nat.log 2 n / 4) := hn₀ n hn

/-- Concrete-threshold binomial lower bound: for n ≥ 2^40,
    C(n/30, log₂ n) ≥ n^(log₂ n / 4).
    Eliminates the existential quantifier from binomial_lower_bound'. -/
theorem binomial_lower_bound_concrete (n : ℕ) (hn : n ≥ 2 ^ 20) :
    Nat.choose (n / 30) (Nat.log 2 n) ≥ n ^ (Nat.log 2 n / 4) := by
  by_cases hk0 : Nat.log 2 n = 0
  · simp [hk0]
  · have hk_pos := Nat.pos_of_ne_zero hk0
    set k := Nat.log 2 n with hk_def
    -- poly_beats_log core: (n / (30 * k))^k ≥ n^(k/4) for n ≥ 2^40
    have hpbl : (n / 30 / k) ^ k ≥ n ^ (k / 4) := by
      rw [Nat.div_div_eq_div_mul]
      have hq4 := quotient_pow4_ge n hn
      have hk20 : 20 ≤ k := by
        have h1 : Nat.log 2 (2^20) = 20 := Nat.log_pow (by norm_num) 20
        have h2 : Nat.log 2 (2^20) ≤ k := Nat.log_mono (by norm_num) le_rfl hn
        omega
      have hq1 : 1 ≤ n / (30 * k) := by
        apply Nat.div_pos
        · calc 30 * k ≤ 2 ^ (k / 2) := thirty_k_le_pow_half k (by omega)
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ ≤ n := Nat.pow_log_le_self 2 (by omega)
        · omega
      exact pow_lift_four _ n k hq4 hq1
    calc Nat.choose (n / 30) k
        ≥ (n / 30 / k) ^ k := choose_ge_div_pow _ _ hk_pos
      _ ≥ n ^ (k / 4) := hpbl

end BinomialBound
