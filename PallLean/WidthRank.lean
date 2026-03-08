/-
  WidthRank.lean — §9 Width⇒Rank Theorem (Theorem 23)

  Generic Width⇒Rank assembly: given a polynomial with a profile
  decomposition (bounded profile count + per-profile dimension),
  proves the SPDP rank is polynomial in n.

  Uses ProfileCompression.choose_le_pow for the combinatorial bounds.
  The compiler-specific axiom is in FullCompiler.lean.
-/
import PallLean.SPDPDefs
import PallLean.ProfileCompression
import Mathlib.Tactic

namespace WidthRank

open SPDP ProfileCompression

/-! ## Generic Width⇒Rank Assembly

    Given:
    - Γ ≤ C(R+m, m) · C(R+D, D)  (profile decomposition)
    - R ≤ n                        (CEW bound)
    - m, D ≥ 1                     (compiler constants)
    Proves: Γ ≤ n^(m+D+1) for n ≥ 2^(m+D).

    This is the paper's Theorem 23 / Lemma 32 assembly step. -/

/-- (n+1)^k ≤ n^(k+1) for n ≥ 2^k.
    Proof: (n+1)^k ≤ (2n)^k = 2^k · n^k ≤ n · n^k = n^(k+1). -/
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

/-- Width⇒Rank assembly: profile decomposition → polynomial rank bound.

    If Γ ≤ C(R+m, m) · C(R+D, D) and R ≤ n, then Γ ≤ n^(m+D+1)
    for n ≥ 2^(m+D). -/
theorem profile_to_poly_bound {Γ R n m D : ℕ}
    (hm : m ≥ 1) (hD : D ≥ 1)
    (hR : R ≤ n)
    (hn : n ≥ 2 ^ (m + D))
    (hΓ : Γ ≤ Nat.choose (R + m) m * Nat.choose (R + D) D) :
    Γ ≤ n ^ (m + D + 1) := by
  have h1 : Nat.choose (R + m) m ≤ (R + 1) ^ m := choose_le_pow R m
  have h2 : Nat.choose (R + D) D ≤ (R + 1) ^ D := choose_le_pow R D
  calc Γ
      ≤ Nat.choose (R + m) m * Nat.choose (R + D) D := hΓ
    _ ≤ (R + 1) ^ m * (R + 1) ^ D := Nat.mul_le_mul h1 h2
    _ = (R + 1) ^ (m + D) := by ring
    _ ≤ (n + 1) ^ (m + D) := Nat.pow_le_pow_left (by omega) (m + D)
    _ ≤ n ^ (m + D + 1) := succ_pow_le_pow_succ n (m + D) hn

end WidthRank
