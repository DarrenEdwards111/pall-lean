/-
  WidthRank.lean — §9 Width⇒Rank Assembly (generic arithmetic)

  Pure arithmetic lemmas for the Width⇒Rank assembly.
  The compiler-specific axiom lives in FullCompiler.lean.
-/
import PallLean.SPDPDefs
import PallLean.ProfileCompression
import Mathlib.Tactic

namespace WidthRank

open ProfileCompression

/-! ## Assembly Lemmas -/

/-- (n+1)^k ≤ n^(k+1) for n ≥ 2^k -/
theorem succ_pow_le_pow_succ (n k : ℕ) (hn : n ≥ 2 ^ k) :
    (n + 1) ^ k ≤ n ^ (k + 1) := by
  calc (n + 1) ^ k
      ≤ (2 * n) ^ k := by
        apply Nat.pow_le_pow_left
        have : n ≥ 1 := le_trans (Nat.one_le_pow k 2 (by omega)) hn
        omega
    _ = 2 ^ k * n ^ k := by ring
    _ ≤ n * n ^ k := Nat.mul_le_mul_right _ hn
    _ = n ^ (k + 1) := by ring

/-- Profile decomposition → polynomial rank bound.
    If Γ ≤ numP * maxD, numP ≤ C(R+m,m), maxD ≤ C(R+D,D), R ≤ n,
    then Γ ≤ n^(m+D+1). -/
theorem profile_to_poly_bound {Γ R n m D numP maxD : ℕ}
    (hm : m ≥ 1) (hD : D ≥ 1)
    (hR : R ≤ n)
    (hn : n ≥ 2 ^ (m + D))
    (hΓ : Γ ≤ numP * maxD)
    (hP : numP ≤ Nat.choose (R + m) m)
    (hDim : maxD ≤ Nat.choose (R + D) D) :
    Γ ≤ n ^ (m + D + 1) := by
  have h1 : Nat.choose (R + m) m ≤ (R + 1) ^ m := choose_le_pow R m
  have h2 : Nat.choose (R + D) D ≤ (R + 1) ^ D := choose_le_pow R D
  calc Γ
      ≤ numP * maxD := hΓ
    _ ≤ Nat.choose (R + m) m * Nat.choose (R + D) D := Nat.mul_le_mul hP hDim
    _ ≤ (R + 1) ^ m * (R + 1) ^ D := Nat.mul_le_mul h1 h2
    _ = (R + 1) ^ (m + D) := by ring
    _ ≤ (n + 1) ^ (m + D) := Nat.pow_le_pow_left (by omega) (m + D)
    _ ≤ n ^ (m + D + 1) := succ_pow_le_pow_succ n (m + D) hn

end WidthRank
