/-
  ProfileCompression.lean — §9 sub-axioms (no FullCompiler dependency)

  Pure mathematical facts about profiles, independent of compiler details.
  The compiler-specific assembly (A4) lives in FullCompiler.lean.
-/
import PallLean.SPDPDefs
import Mathlib.Tactic

namespace ProfileCompression

/-! ## Axiom 1: Profile Count Bound (§9.1, Lemma 20)

    Stars-and-bars: weak compositions of R into m+1 parts.
    |H(R)| ≤ C(R+m, m) ≤ (R+1)^m where m = |T| = O(1). -/
axiom profile_count_bound :
    ∃ m, m ≥ 1 ∧ ∀ R, Nat.choose (R + m) m ≤ (R + 1) ^ m

/-! ## Axiom 2: Within-Profile Dimension (§9.1, Lemma 22)

    dim(Sym^k(W)) = C(k+d-1,d-1) where d = dim(W).
    For V_h = ⊗_τ Sym^{h(τ)}(W_τ):
    dim(V_h) = Π_τ C(h(τ)+d_τ-1,d_τ-1) ≤ (R+1)^{Σ(d_τ-1)} = (R+1)^D. -/
axiom within_profile_dim_bound :
    ∃ D, D ≥ 1 ∧ ∀ k d, d ≥ 1 →
      Nat.choose (k + d - 1) (d - 1) ≤ (k + 1) ^ (d - 1)

/-! ## Lemma: polylog^const ≤ n^const for large n

    ((log₂ n)^E + 1)^E ≤ n^{E+1} for n ≥ 2^{E^E}
    because log₂ n < n^{1/E} for large n,
    so (log₂ n)^E + 1 ≤ n, so ((...)^E ≤ n^E ≤ n^{E+1}. -/
axiom polylog_pow_le (E : ℕ) (hE : E ≥ 1) :
    ∃ n₀, ∀ n ≥ n₀,
      ((Nat.log 2 n) ^ E + 1) ^ E ≤ n ^ (E + 1)

end ProfileCompression
