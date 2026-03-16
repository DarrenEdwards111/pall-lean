/-
  SwitchingLemma.lean — Universal SPDP Collapse (Paper Theorem 7.3)

  Proof chain:
  1. BoolCircuit.switching_spdp_bound: SPDP rank ≤ (log₂ n + 1)²
  2. polylog_sq_le_sqrt: (log₂ n + 1)² ≤ √n for n ≥ 2^17
  3. Combine: SPDP rank ≤ √n for n ≥ 2^17
-/
import PallLean.SPDPDefs
import PallLean.RestrictedSPDP
import PallLean.Restriction
import PallLean.UniversalRestriction
import PallLean.Depth4Simulation
import PallLean.BoolEval
import PallLean.TuringMachine
import PallLean.BoolCircuit
import Mathlib.Tactic

namespace SwitchingLemma

open MvPolynomial SPDP RestrictedSPDP Restriction Depth4Simulation BoolEval

/-! ## Polylog ≤ √n for large n -/

private lemma pow4_le_exp2_step (k : ℕ) (hk : k ≥ 17) :
    (k + 2) ^ 4 ≤ 2 * (k + 1) ^ 4 := by
  suffices h : ((k + 2 : ℤ)) ^ 4 ≤ 2 * ((k + 1 : ℤ)) ^ 4 by exact_mod_cast h
  have hk' : (k : ℤ) ≥ 17 := by exact_mod_cast hk
  nlinarith [sq_nonneg (k : ℤ), sq_nonneg ((k : ℤ) * k), sq_nonneg ((k : ℤ) * k - 12)]

/-- (k+1)^4 ≤ 2^k for k ≥ 17. Exponential beats polynomial. -/
private lemma pow4_le_exp2 (k : ℕ) (hk : k ≥ 17) : (k + 1) ^ 4 ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk17 : k ≥ 17
    · calc (k + 1 + 1) ^ 4 = (k + 2) ^ 4 := by ring_nf
        _ ≤ 2 * (k + 1) ^ 4 := pow4_le_exp2_step k hk17
        _ ≤ 2 * 2 ^ k := by linarith [ih hk17]
        _ = 2 ^ (k + 1) := by ring
    · interval_cases k <;> omega

/-- (log₂ n + 1)^4 ≤ n for n ≥ 2^17. -/
private lemma log_pow4_le (n : ℕ) (hn : n ≥ 2 ^ 17) :
    (Nat.log 2 n + 1) ^ 4 ≤ n := by
  have h17 : Nat.log 2 n ≥ 17 :=
    le_trans (by native_decide : 17 ≤ Nat.log 2 (2^17)) (Nat.log_mono_right hn)
  calc (Nat.log 2 n + 1) ^ 4
      ≤ 2 ^ Nat.log 2 n := pow4_le_exp2 _ h17
    _ ≤ n := Nat.pow_log_le_self 2 (by omega)

/-- (log₂ n + 1)² ≤ √n for n ≥ 2^17. -/
private lemma polylog_sq_le_sqrt :
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    (Nat.log 2 n + 1) ^ 2 ≤ Nat.sqrt n := by
  exact ⟨2 ^ 17, fun n hn => by
    rw [Nat.le_sqrt]
    calc (Nat.log 2 n + 1) ^ 2 * (Nat.log 2 n + 1) ^ 2
        = (Nat.log 2 n + 1) ^ 4 := by ring
      _ ≤ n := log_pow4_le n hn⟩

/-- Paper Theorem 7.3 (Universal SPDP Collapse):
    For sufficiently large n, every DTM-decidable function has
    restricted SPDP rank ≤ √n under the universal restriction ρ*.

    Proof: switching_spdp_bound gives rank ≤ (log₂ n + 1)²,
    and polylog_sq_le_sqrt gives (log₂ n + 1)² ≤ √n. -/
theorem universal_spdp_collapse :
    ∃ n₀ : ℕ, ∀ (n : ℕ), n ≥ n₀ → n ≥ 2 →
    ∀ (f : (Fin n → Bool) → Bool)
      (M : TuringMachine.DTM) (_ : M.decides f),
    restrictedSpdpRank (Nat.log 2 n) (Nat.log 2 n)
      (Depth4Simulation.multilinearInterp f)
      (UniversalRestriction.universalRestriction n) ≤ Nat.sqrt n := by
  obtain ⟨n₀, hn₀⟩ := polylog_sq_le_sqrt
  exact ⟨n₀, fun n h_ge _h2 f M hM =>
    le_trans (BoolCircuit.switching_spdp_bound f M hM (by omega)) (hn₀ n h_ge)⟩

end SwitchingLemma
