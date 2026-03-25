import PallLean.IdentityMinorProof
import Mathlib.Tactic

theorem layer3_proof (α : ℕ) (hα : α ≥ 1) (c : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, n ≥ 2 →
    Nat.choose (α * n) (Nat.log 2 n) > n ^ c := by
  refine ⟨2 ^ (c + 2) * (Nat.factorial (c + 1) + 1), fun n hn hn2 => ?_⟩
  have hfp := Nat.factorial_pos (c + 1)
  have hn_big : n ≥ 2 ^ (c + 2) := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hn
  have hlog : Nat.log 2 n ≥ c + 1 := by
    calc Nat.log 2 n ≥ Nat.log 2 (2 ^ (c + 2)) := Nat.log_mono_right hn_big
      _ = c + 2 := by rw [Nat.log_pow]; norm_num
      _ ≥ c + 1 := by omega
  have hαn : α * n ≥ n := Nat.le_mul_of_pos_left n (by omega)
  have hlog_lt : Nat.log 2 n < n := by
    exact Nat.log_lt_of_lt_pow (show n ≠ 0 by omega) (Nat.lt_pow_self (show 1 < 2 from by omega))
  -- All threshold facts from n ≥ 2^(c+2) * ((c+1)!+1)
  -- These are concrete Nat arithmetic: 2^c ≥ c, products of large numbers, log < n.
  have pow2_ge : ∀ k, 2 ^ k ≥ k := fun k => by
    induction k with | zero => simp | succ k ih => linarith [show 2^(k+1) = 2^k+2^k from by ring, Nat.one_le_pow k 2 (by omega)]
  have hn2c : n ≥ 2 * c := by linarith [show 2^(c+2) ≥ 4*c from by linarith [show 2^(c+2)=4*2^c from by ring, Nat.mul_le_mul_left 4 (pow2_ge c)]]
  have hαnc : α * n - c > 2 ^ c * Nat.factorial (c + 1) := by
    have h_eq : 2 ^ (c + 2) = 4 * 2 ^ c := by ring
    have h_n : n ≥ 4 * 2 ^ c * (Nat.factorial (c + 1) + 1) := by linarith [h_eq ▸ hn]
    have : n ≥ 2 ^ c * Nat.factorial (c + 1) + c + 1 := by nlinarith [pow2_ge c, hfp]
    omega
  have hαn_mono : α * n ≥ 2 * Nat.log 2 n + 1 := by
    -- n ≥ 8 → 2*log₂ n + 1 ≤ n → αn ≥ n ≥ 2*log n + 1.
    -- 2*log₂ n + 1 ≤ n: from 2^k ≥ 2k+1 for k = log₂ n ≥ 3.
    have hn8 : n ≥ 8 := by
      have := Nat.mul_le_mul (Nat.one_le_pow (c+2) 2 (by omega)) (show 1 ≤ Nat.factorial (c+1)+1 from by omega)
      have : (2:ℕ)^2 ≤ 2^(c+2) := Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith
    -- 2^k ≥ 2k+1 for k ≥ 3 (induction)
    have pow2_ge_2k1 : ∀ k, k ≥ 3 → 2 ^ k ≥ 2 * k + 1 := by
      intro k hk; induction k with
      | zero => omega
      | succ k ih =>
        by_cases hk3 : k ≥ 3
        · have := ih hk3; linarith [show 2^(k+1)=2^k+2^k from by ring, Nat.one_le_pow k 2 (by omega)]
        · interval_cases k <;> omega
    have hlog3 : Nat.log 2 n ≥ 3 := by
      calc Nat.log 2 n ≥ Nat.log 2 8 := Nat.log_mono_right hn8
        _ = 3 := by native_decide
    -- 2^(log n) ≤ n and 2^(log n) ≥ 2*(log n)+1
    have hpow := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    have h2k := pow2_ge_2k1 (Nat.log 2 n) hlog3
    linarith [hαn]
  -- Main proof (structure PROVED, threshold sorries above)
  have hmono := choose_mono_iter (α * n) (c + 1) (Nat.log 2 n) hlog (by omega)
  have hfact := choose_factorial_ge (α * n) (c + 1) (by omega)
  have h1 : n ≤ 2 * (α * n - c) := by omega
  have h2 : n ^ c ≤ 2 ^ c * (α * n - c) ^ c :=
    (Nat.mul_pow 2 (α * n - c) c) ▸ Nat.pow_le_pow_left h1 c
  have hpos : 0 < (α * n - c) ^ c :=
    Nat.pos_of_ne_zero (by intro h; simp [Nat.pow_eq_zero] at h; omega)
  have h_key : (α * n - c) ^ (c + 1) > n ^ c * Nat.factorial (c + 1) := by
    have := Nat.mul_lt_mul_of_pos_left hαnc hpos
    have : (α * n - c) ^ c * (α * n - c) = (α * n - c) ^ (c + 1) := pow_succ ..
    linarith [Nat.mul_le_mul_right (Nat.factorial (c + 1)) h2]
  have h_choose : Nat.choose (α * n) (c + 1) > n ^ c := by
    by_contra h; push_neg at h
    have h_mul := Nat.mul_le_mul_right (Nat.factorial (c + 1)) h
    have : (α * n - (c + 1) + 1) = α * n - c := by omega
    rw [this] at hfact; linarith
  linarith
