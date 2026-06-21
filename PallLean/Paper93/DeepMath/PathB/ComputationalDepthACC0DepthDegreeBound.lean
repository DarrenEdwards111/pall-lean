import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ParityBarrier

/-!
# Brick (depth→degree) — `MOD_2 ∉` constant-depth `AC⁰[p]` for odd `p` (proved)

The depth→degree blow-up that upgrades the bounded-*degree* separation (Brick parity barrier) to a bounded-*depth* one.
Because the `AND`/`OR` gates are binary, the representation degree at most doubles per level, so `reprDegP C ≤ (p−1)·2^{depth
C}` (`reprDegP_le_depth`).  Hence a depth-`d` `AC⁰[p]` circuit has degree `≤ (p−1)·2^d`, and once `(p−1)·2^d < n` the
low-degree barrier kills `MOD_2`: `MOD_2 ∉` depth-`d` `AC⁰[p]` (`parity_not_acc0p_depth`).

For *constant* depth `d` and fixed odd `p`, `(p−1)·2^d` is a constant, so for all large `n` this is the genuine
Razborov–Smolensky separation `MOD_2 ∉ AC⁰[p]` at constant depth — the standard form, here with an explicit `n`-threshold.

## What is proved (clean axioms, no `sorry`)

* **`reprDegP_le_depth`** (PROVED) — `reprDegP p C ≤ (p−1) · 2^{depth C}`.
* **`parity_not_acc0p_depth`** (PROVED) — `p≠2 → (p−1)·2^d < n → ¬∃ C, ModpOnly p C ∧ depth C ≤ d ∧ eval C = MOD_2`.

## Honest scope

The `q=2` RS separation against constant-*depth* `AC⁰[p]` (any size, since the bound is depth-only — `reprDegP` ignores
fan-out/repeated subcircuits, and the inductive `ACC0Circuit` is a formula).  It does **not** cover general `MOD_q` (`q>2`)
nor the Williams cash-out to `NEXP ⊄ ACC⁰`.  General YBT and `NEXP ⊄ ACC⁰` remain open.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0DepthDegreeBound

open PallLean.Paper93.DeepMath.PathB.ACC0CircuitModel (ACC0Circuit depth)
open PallLean.Paper93.DeepMath.PathB.ACC0CircuitReprP (reprDegP ModpOnly)
open PallLean.Paper93.DeepMath.PathB.ACC0ParityBarrier (parityFn parityFn_not_acc0p)

variable {n p : ℕ} [Fact p.Prime]

/-- **Depth→degree blow-up (PROVED): `reprDegP C ≤ (p−1)·2^{depth C}`.** -/
theorem reprDegP_le_depth (C : ACC0Circuit n) : reprDegP p C ≤ (p - 1) * 2 ^ (depth C) := by
  induction C with
  | const b => simp only [reprDegP, depth]; exact Nat.zero_le _
  | var i =>
      simp only [reprDegP, depth, pow_zero, mul_one]
      have := (Fact.out : p.Prime).two_le; omega
  | not c ih =>
      simp only [reprDegP, depth]
      exact le_trans ih (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega)))
  | and a b iha ihb =>
      simp only [reprDegP, depth]
      have h1 : 2 ^ depth a ≤ 2 ^ max (depth a) (depth b) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h2 : 2 ^ depth b ≤ 2 ^ max (depth a) (depth b) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      calc reprDegP p a + reprDegP p b
          ≤ (p - 1) * 2 ^ depth a + (p - 1) * 2 ^ depth b := add_le_add iha ihb
        _ ≤ (p - 1) * 2 ^ max (depth a) (depth b) + (p - 1) * 2 ^ max (depth a) (depth b) := by gcongr
        _ = (p - 1) * 2 ^ (1 + max (depth a) (depth b)) := by rw [pow_add]; ring
  | or a b iha ihb =>
      simp only [reprDegP, depth]
      have h1 : 2 ^ depth a ≤ 2 ^ max (depth a) (depth b) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h2 : 2 ^ depth b ≤ 2 ^ max (depth a) (depth b) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      calc reprDegP p a + reprDegP p b
          ≤ (p - 1) * 2 ^ depth a + (p - 1) * 2 ^ depth b := add_le_add iha ihb
        _ ≤ (p - 1) * 2 ^ max (depth a) (depth b) + (p - 1) * 2 ^ max (depth a) (depth b) := by gcongr
        _ = (p - 1) * 2 ^ (1 + max (depth a) (depth b)) := by rw [pow_add]; ring
  | mod q S t => simp only [reprDegP, depth, pow_one]; omega

/-- **`MOD_2 ∉` constant-depth `AC⁰[p]` for odd `p` (PROVED).** -/
theorem parity_not_acc0p_depth (hp2 : p ≠ 2) {d : ℕ} (hd : (p - 1) * 2 ^ d < n) :
    ¬ ∃ C : ACC0Circuit n, ModpOnly p C ∧ depth C ≤ d ∧ ACC0CircuitModel.eval C = parityFn := by
  rintro ⟨C, hmod, hdep, hev⟩
  have hbound : reprDegP p C ≤ (p - 1) * 2 ^ d :=
    le_trans (reprDegP_le_depth C) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hdep))
  exact parityFn_not_acc0p hp2 (lt_of_le_of_lt hbound hd) ⟨C, hmod, le_refl _, hev⟩

/-!
**The constant-depth separation, proved.**  `reprDegP` blows up by at most `(p−1)·2^{depth}`, so for `(p−1)·2^d < n` no
depth-`d` `AC⁰[p]` circuit computes `MOD_2` — the standard `q=2` Razborov–Smolensky separation at constant depth, with an
explicit `n`-threshold.  Remaining (open, not faked): general `MOD_q` (`q>2`) and the Williams cash-out.  Not `NEXP ⊄ ACC⁰`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0DepthDegreeBound

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DepthDegreeBound.reprDegP_le_depth
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0DepthDegreeBound.parity_not_acc0p_depth
