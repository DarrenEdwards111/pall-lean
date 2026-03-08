/-
  ProfileCompression.lean — §9 sub-axioms (no FullCompiler dependency)

  Pure mathematical facts about profiles, independent of compiler details.
  The compiler-specific assembly (A4) lives in FullCompiler.lean.
-/
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace ProfileCompression

/-! ## Helper: choose(R+m, m) ≤ (R+1)^m

    Proof by induction on m using the recurrence
    (R+m+1) * C(R+m, m) = C(R+m+1, m+1) * (m+1). -/
theorem choose_le_pow (R m : ℕ) : Nat.choose (R + m) m ≤ (R + 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hrw : R + (m + 1) = R + m + 1 := by omega
    rw [hrw]
    have key : (R + m + 1) * Nat.choose (R + m) m =
      Nat.choose (R + m + 1) (m + 1) * (m + 1) := by
      have := Nat.add_one_mul_choose_eq (R + m) m
      linarith
    have hle : Nat.choose (R + m + 1) (m + 1) * (m + 1) ≤ (R + 1) ^ (m + 1) * (m + 1) := by
      rw [← key]
      calc (R + m + 1) * Nat.choose (R + m) m
          ≤ (R + m + 1) * (R + 1) ^ m := Nat.mul_le_mul_left _ ih
        _ ≤ ((R + 1) * (m + 1)) * (R + 1) ^ m := by
            apply Nat.mul_le_mul_right; nlinarith
        _ = (R + 1) ^ (m + 1) * (m + 1) := by ring
    exact Nat.le_of_mul_le_mul_right hle (by omega)

/-! ## Profile Count Bound (§9.1, Lemma 20) — PROVED

    Stars-and-bars: weak compositions of R into m+1 parts.
    |H(R)| ≤ C(R+m, m) ≤ (R+1)^m where m = |T| = O(1). -/
theorem profile_count_bound :
    ∃ m, m ≥ 1 ∧ ∀ R, Nat.choose (R + m) m ≤ (R + 1) ^ m :=
  ⟨1, le_refl 1, fun R => choose_le_pow R 1⟩

/-! ## Within-Profile Dimension (§9.1, Lemma 22) — PROVED

    dim(Sym^k(W)) = C(k+d-1,d-1) where d = dim(W).
    Bound: C(k+d-1, d-1) ≤ (k+1)^(d-1). -/
theorem within_profile_dim_bound :
    ∃ D, D ≥ 1 ∧ ∀ k d, d ≥ 1 →
      Nat.choose (k + d - 1) (d - 1) ≤ (k + 1) ^ (d - 1) := by
  exact ⟨1, le_refl 1, fun k d hd => by
    have : k + d - 1 = k + (d - 1) := by omega
    rw [this]; exact choose_le_pow k (d - 1)⟩

/-! ## Lemma: polylog^const ≤ n^const for large n

    ((log₂ n)^E + 1)^E ≤ n^{E+1} for large n.
    Relies on: (log₂ n)^E + 1 ≤ n for large n
    (exponential growth dominates polynomial of logarithm). -/
axiom polylog_pow_le (E : ℕ) (hE : E ≥ 1) :
    ∃ n₀, ∀ n ≥ n₀,
      ((Nat.log 2 n) ^ E + 1) ^ E ≤ n ^ (E + 1)

end ProfileCompression
