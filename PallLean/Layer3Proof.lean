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
  have pow2_ge : ∀ k, 2 ^ k ≥ k := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      linarith [Nat.one_le_pow k 2 (by omega)]
  have hn2c : n ≥ 2 * c := by sorry
  have hαnc : α * n - c > 2 ^ c * Nat.factorial (c + 1) := by
    have : n ≥ 4 * 2 ^ c * (Nat.factorial (c + 1) + 1) := by nlinarith [show 2 ^ (c + 2) = 4 * 2 ^ c from by ring]
    sorry
  have hlog_lt : Nat.log 2 n < n := by
    apply Nat.log_lt_of_lt_pow (by omega)
    exact Nat.lt_pow_self (show 1 < 2 from by omega)
  have hαn_mono : α * n ≥ 2 * Nat.log 2 n + 1 := by sorry
  have hmono := choose_mono_iter (α * n) (c + 1) (Nat.log 2 n) hlog (by omega)
  have hfact := choose_factorial_ge (α * n) (c + 1) (by omega)
  have h1 : n ≤ 2 * (α * n - c) := by omega
  have h2 : n ^ c ≤ 2 ^ c * (α * n - c) ^ c :=
    (Nat.mul_pow 2 (α * n - c) c) ▸ Nat.pow_le_pow_left h1 c
  have hpos : 0 < (α * n - c) ^ c :=
    Nat.pos_of_ne_zero (by intro h; simp [Nat.pow_eq_zero] at h; omega)
  have h_key : (α * n - c) ^ (c + 1) > n ^ c * Nat.factorial (c + 1) := by
    have step1 := Nat.mul_lt_mul_of_pos_left hαnc hpos
    have step2 : (α * n - c) ^ c * (α * n - c) = (α * n - c) ^ (c + 1) := pow_succ ..
    linarith [Nat.mul_le_mul_right (Nat.factorial (c + 1)) h2]
  have h_choose : Nat.choose (α * n) (c + 1) > n ^ c := by
    by_contra h; push_neg at h
    have h_mul := Nat.mul_le_mul_right (Nat.factorial (c + 1)) h
    have : (α * n - (c + 1) + 1) = α * n - c := by omega
    rw [this] at hfact; linarith
  linarith
