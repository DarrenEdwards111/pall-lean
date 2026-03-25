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
  -- Threshold arithmetic (TODO: prove from hn)
  have hn2c : n ≥ 2 * c := by sorry
  have hαnc : α * n - c > 2 ^ c * Nat.factorial (c + 1) := by sorry
  have hαn_mono : α * n ≥ 2 * Nat.log 2 n + 1 := by sorry
  -- Step A: monotonicity
  have hmono := choose_mono_iter (α * n) (c + 1) (Nat.log 2 n) hlog (by omega)
  -- Step B: factorial bound
  have hfact := choose_factorial_ge (α * n) (c + 1) (by omega)
  -- Step C: key inequality
  have h1 : n ≤ 2 * (α * n - c) := by omega
  have h2 : n ^ c ≤ 2 ^ c * (α * n - c) ^ c :=
    (Nat.mul_pow 2 (α * n - c) c) ▸ Nat.pow_le_pow_left h1 c
  have hpos : 0 < (α * n - c) ^ c :=
    Nat.pos_of_ne_zero (by intro h; simp [Nat.pow_eq_zero] at h; omega)
  have h_key : (α * n - c) ^ (c + 1) > n ^ c * Nat.factorial (c + 1) := by
    have step1 : (α * n - c) ^ c * (α * n - c) >
        (α * n - c) ^ c * (2 ^ c * Nat.factorial (c + 1)) :=
      Nat.mul_lt_mul_of_pos_left hαnc hpos
    have step2 : (α * n - c) ^ c * (α * n - c) = (α * n - c) ^ (c + 1) := by
      rw [pow_succ]
    linarith [step2, Nat.mul_le_mul_right (Nat.factorial (c + 1)) h2]
  -- Step D: C(αn, c+1) > n^c
  have h_choose : Nat.choose (α * n) (c + 1) > n ^ c := by
    by_contra h; push_neg at h
    have h_mul := Nat.mul_le_mul_right (Nat.factorial (c + 1)) h
    -- h_mul: C(αn,c+1) * (c+1)! ≤ n^c * (c+1)!
    -- hfact: C(αn,c+1) * (c+1)! ≥ (αn-c+1)^(c+1) ≥ (αn-c)^(c+1) (since αn-c+1 > αn-c)
    -- h_key: (αn-c)^(c+1) > n^c * (c+1)!
    -- Chain: n^c*(c+1)! ≥ C*(c+1)! ≥ (αn-c+1)^(c+1) ≥ ... WRONG direction.
    -- Actually: hfact says C*(c+1)! ≥ (αn-(c+1)+1)^(c+1) = (αn-c)^(c+1).
    -- h_mul says C*(c+1)! ≤ n^c*(c+1)!.
    -- Combined: (αn-c)^(c+1) ≤ C*(c+1)! ≤ n^c*(c+1)!. But h_key says (αn-c)^(c+1) > n^c*(c+1)!.
    -- Contradiction!
    have : (α * n - (c + 1) + 1) = α * n - c := by omega
    rw [this] at hfact
    linarith
  -- Combined
  linarith
