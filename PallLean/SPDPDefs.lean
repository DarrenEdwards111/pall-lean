import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
/-!
# SPDP Definitions — Pall §2
-/

namespace SPDP

structure BlockPartition (n : ℕ) where
  numBlocks : ℕ
  assign : Fin n → Fin numBlocks

structure SPDPParams where
  κ : ℕ
  ℓ : ℕ

def matchedParams (n : ℕ) : SPDPParams :=
  { κ := Nat.log 2 n, ℓ := Nat.log 2 n }

opaque spdpRank {F : Type*} [Field F] (n : ℕ) (params : SPDPParams)
    (B : BlockPartition n) (p : MvPolynomial (Fin n) F) : ℕ

theorem superPoly_beats_poly (C : ℕ) (hC : C ≥ 1) :
    ∃ n₀, ∀ n, n ≥ n₀ → n ^ (Nat.log 2 n / 4) > n ^ C := by
  use 2 ^ (4 * C + 4)
  intro n hn
  apply Nat.pow_lt_pow_right
  · have : (2 : ℕ) ^ 1 ≤ 2 ^ (4 * C + 4) := by
      apply Nat.pow_le_pow_right (by norm_num)
      omega
    omega
  · have h_log : Nat.log 2 n ≥ 4 * C + 4 := by
      have h1 : Nat.log 2 (2 ^ (4 * C + 4)) = 4 * C + 4 :=
        Nat.log_pow (by norm_num : 1 < 2) (4 * C + 4)
      have h2 : Nat.log 2 n ≥ Nat.log 2 (2 ^ (4 * C + 4)) :=
        Nat.log_mono_right hn
      omega
    omega

end SPDP
