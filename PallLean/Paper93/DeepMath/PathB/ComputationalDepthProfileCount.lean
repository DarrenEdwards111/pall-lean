import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer7CircuitFamily

/-!
# Route F — the "polynomially many profiles" bound (proved)

The load-bearing combinatorial component of `CookLevinFrontierHyp` (Route F): the Cook–Levin compilation is
classified into "profiles," and the bound `#profiles ≤ poly(n)` is needed (together with the within-profile
finrank bound) to get total SPDP rank `≤ n²⁰⁰`.

The honest reading of "polynomially many profiles" — the *load-bearing* one, not the trivial local-window
count — is the paper's `(3 log n + 1)¹²`-style bound: **a profile determined by `O(log n)` cells over a
fixed finite alphabet has only polynomially-many distinct values.**  That is proved here.

* `pow_log_le_pow` — the heart: `s^(log₂ n) ≤ n^(log₂ s + 1)` (a constant raised to `log n` stays
  polynomial in `n`).
* `profile_count_le_poly` — `s^(c·log₂ n) ≤ n^(c·(log₂ s + 1))`.
* `profileSpace_card_le_poly` — a profile space `Fin (c·log₂ n) → α` (`α` finite) has card `≤ poly(n)`.
* `profileCount_isPolyBounded` — `n ↦ |α|^(c·log₂ n)` is `IsPolyBounded`.

## What this does and does not close

**Proved:** *if* a profile is an `O(log n)`-cell window over a fixed alphabet, then there are `≤ poly(n)`
profiles.  This is the "bounded number of profiles" half of Route F's `totalProfileBound`, now a theorem.

**Still open (the two remaining inputs of `CookLevinFrontierHyp`), kept explicit, never asserted:**
1. **Locality input** — the *actual* Cook–Levin compilation's profile is genuinely an `O(log n)`-cell
   window over a fixed alphabet.  This is a structural claim about the compilation; the documented P-side
   gap (product sheets / lane classification) lives here — the naive locality counting does **not** transfer
   to the SPDP partition rows for free.
2. **Within-profile finrank** — `CookLevinExactWithinProfileFinrankLemma`: each profile contributes finrank
   `≤ (3 log n + 1)¹²`.  This is the audit's load-bearing socket.

So this file discharges the *counting* half cleanly and pins the remaining difficulty to (1)+(2) — neither
of which a profile count establishes.
-/

namespace PallLean.Paper93.DeepMath.PathB.ProfileCount

open PallLean.Paper93.DeepMath.PathB

/-- **The combinatorial heart:** `s^(log₂ n) ≤ n^(log₂ s + 1)` — exponentiating a constant by `log n` stays
polynomial in `n` (since `s ≤ 2^{log₂ s + 1}` and `2^{log₂ n} ≤ n`). -/
theorem pow_log_le_pow (s n : ℕ) (hn : 1 ≤ n) :
    s ^ (Nat.log 2 n) ≤ n ^ (Nat.log 2 s + 1) := by
  calc s ^ (Nat.log 2 n)
      ≤ (2 ^ (Nat.log 2 s + 1)) ^ (Nat.log 2 n) :=
        Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self (by norm_num) s).le _
    _ = (2 ^ (Nat.log 2 n)) ^ (Nat.log 2 s + 1) := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ n ^ (Nat.log 2 s + 1) :=
        Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) _

/-- `s^(c·log₂ n) ≤ n^(c·(log₂ s + 1))` — a constant `s` raised to `c·log₂ n` is bounded by a fixed
polynomial in `n`. -/
theorem profile_count_le_poly (s c n : ℕ) (hn : 1 ≤ n) :
    s ^ (c * Nat.log 2 n) ≤ n ^ (c * (Nat.log 2 s + 1)) := by
  rw [Nat.mul_comm c (Nat.log 2 n), pow_mul, Nat.mul_comm c (Nat.log 2 s + 1), pow_mul]
  exact Nat.pow_le_pow_left (pow_log_le_pow s n hn) c

/-- A **profile space** — windows of `c·log₂ n` cells over a finite alphabet `α` — has at most
`n^(c·(log₂|α|+1))` distinct profiles: **polynomially many.** -/
theorem profileSpace_card_le_poly (α : Type*) [Fintype α] (c n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (Fin (c * Nat.log 2 n) → α) ≤ n ^ (c * (Nat.log 2 (Fintype.card α) + 1)) := by
  rw [Fintype.card_fun, Fintype.card_fin]
  exact profile_count_le_poly _ _ _ hn

/-- The profile count `n ↦ |α|^(c·log₂ n)` is **polynomially bounded** (fixed alphabet `s`, window width
factor `c`). -/
theorem profileCount_isPolyBounded (s c : ℕ) :
    Layer7.IsPolyBounded (fun n => s ^ (c * Nat.log 2 n)) :=
  ⟨1, c * (Nat.log 2 s + 1), 1, fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.log_zero_right, Nat.mul_zero, pow_zero]; exact Nat.le_add_left 1 _
    · calc s ^ (c * Nat.log 2 n)
          ≤ n ^ (c * (Nat.log 2 s + 1)) := profile_count_le_poly s c n hn
        _ ≤ 1 * n ^ (c * (Nat.log 2 s + 1)) + 1 := by omega⟩

end PallLean.Paper93.DeepMath.PathB.ProfileCount

#print axioms PallLean.Paper93.DeepMath.PathB.ProfileCount.profileSpace_card_le_poly
#print axioms PallLean.Paper93.DeepMath.PathB.ProfileCount.profileCount_isPolyBounded
