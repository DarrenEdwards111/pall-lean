/-
  CompiledBound.lean — P-side compiled SPDP rank bound (§9, Lemma 32)

  Downstream file importing both MultilinearSPDP and ProfileCompression
  to prove the compiled polynomial has polynomial SPDP rank.

  Proof chain:
  1. fullCompiledPoly = verifierSheet + violationPoly
  2. violationPoly has degree ≤ 4 < κ (for κ ≥ 5), killed by mlBlockedSpdpRank_add_lowDeg
  3. verifierSheet = rename(tseitin), so compiled_to_tseitin_rank_transport_le applies
  4. tseitin_spdp_rank_proved gives ≤ n^200 (from ProfileCompression)
  5. n^200 ≤ n^215
-/
import PallLean.MultilinearSPDP
import PallLean.ProfileCompression

namespace MultilinearSPDP

open MvPolynomial SPDP TuringMachine Compiler NPWitness Tseitin

/-- 30 * log₂(n) + 1 ≤ n for n ≥ 512.
    Uses 2^k ≥ 31*k for k ≥ 9. -/
theorem log_linear_bound (n : ℕ) (hn : n ≥ 512) : 30 * Nat.log 2 n + 1 ≤ n := by
  set k := Nat.log 2 n
  have hk_bound : 2 ^ k ≤ n := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
  have hk_ge : k ≥ 9 := by
    calc k = Nat.log 2 n := rfl
      _ ≥ Nat.log 2 512 := Nat.log_mono_right hn
      _ = 9 := by native_decide
  have h31k : 31 * k ≤ 2 ^ k := by
    have : ∀ j : ℕ, j ≥ 9 → 31 * j ≤ 2 ^ j := by
      intro j hj
      induction j with
      | zero => omega
      | succ j' ih =>
        by_cases hj' : j' ≥ 9
        · have ih' := ih hj'
          calc 31 * (j' + 1) = 31 * j' + 31 := by ring
            _ ≤ 2 ^ j' + 2 ^ j' := by
                have : 31 ≤ 2 ^ j' := calc
                  31 ≤ 2 ^ 5 := by norm_num
                  _ ≤ 2 ^ j' := Nat.pow_le_pow_right (by norm_num) (by omega)
                omega
            _ = 2 ^ (j' + 1) := by ring
        · have : j' = 8 := by omega
          subst this; norm_num
    exact this k hk_ge
  omega

/-- Compiled-side profile-compression endpoint (§9, Lemma 32).
    For logarithmic matching parameters, the compiled polynomial has
    polynomial multilinear blocked SPDP rank.

    Requires 30 * κ + 1 ≤ n (holds when n ≥ 512 and κ ≤ log₂ n). -/
theorem compiled_profile_compression_rank_bound (M : DTM) (n : ℕ)
    (hn : n ≥ max 4 M.numStates)
    (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n))
    (κ : ℕ) (hκ : κ ≥ 5) (hκ_le : κ ≤ Nat.log 2 n)
    (hRn : 30 * κ + 1 ≤ n) :
    mlBlockedSpdpRank (compiledPartition M n) κ κ
      (fullCompiledPoly ℚ M n h_le) ≤ n ^ 215 := by
  -- Step 1: violationPoly has degree ≤ 4 < κ ≥ 5, killed by add_lowDeg
  have h_lowdeg : (violationPolyOf ℚ M n).totalDegree < κ := by
    have := violationPolyOf_totalDegree ℚ M n; omega
  rw [show fullCompiledPoly ℚ M n h_le = verifierSheetOf ℚ M n h_le + violationPolyOf ℚ M n
      from rfl,
    mlBlockedSpdpRank_add_lowDeg ℚ (compiledPartition M n) κ κ
      (verifierSheetOf ℚ M n h_le) (violationPolyOf ℚ M n) h_lowdeg]
  -- Step 2: verifierSheet rank ≤ tseitin rank via transport
  have h_transport := compiled_to_tseitin_rank_transport_le M n h_le κ κ
  -- Step 3: tseitin rank ≤ n^200 via profile compression
  have hn4 : n ≥ 4 := by omega
  have hparam : AdmissibleSpdpParams n κ := ⟨hκ, hκ_le⟩
  have h_tseitin := tseitin_spdp_rank_proved n hn4 κ hparam hRn
  -- Chain: compiled ≤ tseitin ≤ n^200 ≤ n^215
  calc mlBlockedSpdpRank (compiledPartition M n) κ κ (verifierSheetOf ℚ M n h_le)
      ≤ mlBlockedSpdpRank (tseitinPartition n) κ κ (tseitinPoly ℚ n) := h_transport
    _ ≤ n ^ 200 := h_tseitin
    _ ≤ n ^ 215 := Nat.pow_le_pow_right (by omega) (by omega)

/-- P-side compiled SPDP rank bound (paper's Lemma 32).
    Regime: matching parameters κ = ℓ, κ ≥ 5, κ ≤ log₂ n, 30κ+1 ≤ n. -/
theorem pside_full_ml_rank_bound (M : DTM) :
    ∃ (C : ℕ), ∀ n, n ≥ max 4 M.numStates →
    ∀ (h_le : npNumVars n ≤ numVars M n (Nat.log 2 n)),
    ∀ (kk : ℕ), kk ≥ 5 → kk ≤ Nat.log 2 n →
    30 * kk + 1 ≤ n →
    mlBlockedSpdpRank (compiledPartition M n) kk kk
      (fullCompiledPoly ℚ M n h_le) ≤ n ^ C := by
  use 215; intro n hn h_le kk hk hk_le hRn
  exact compiled_profile_compression_rank_bound M n hn h_le kk hk hk_le hRn

end MultilinearSPDP
