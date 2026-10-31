import Mathlib

/-!
# The error calibration — closing the `ℕ` bookkeeping from seed error to a `< 2^n/10` circuit error

The error-averaging bridge (`…ACC0ErrorAveraging.exists_good_seed`) gives a fixed seed with
`(card Seed)·E ≤ (card Input)·k`, where `E` is the fixed-seed per-gate input-error count and `k` the per-input
seed-error count.  For the amplified `OR` gate the seed error is a `(1/p)^t` fraction, i.e. `p^t · k = card Seed`
(`amplifiedOrPoly_error`), and `card Input = 2^n`.  This file closes the remaining `ℕ`/division bookkeeping:

* cancel the seed relation to get the per-gate bound `p^t · E ≤ 2^n`;
* with the amplification calibration `p^t > 10·size`, conclude `10·(size·E) ≤ 2^n` — i.e. the whole-circuit error
  `size·E` (from `circuit_error_bound`) is `< 2^n/10`.

## What is proved (clean axioms, no `sorry`)

* **`per_gate_error`** — from `(card Seed)·E ≤ (card Input)·k`, `p^t · k = card Seed`, `card Input = 2^n` (and `k > 0`):
  `p^t · E ≤ 2^n`.
* **`error_calibration`** — from `10·size ≤ p^t` and `p^t · E ≤ 2^n`: `10·(size·E) ≤ 2^n`.  Reading `size·E` as the
  total circuit error (the `circuit_error_bound` conclusion), this is "circuit error `< 2^n/10`".

## Honest scope

Pure `ℕ` arithmetic closing the calibration the rest of the chain flagged; no new conceptual content.  The
`p^t · k = card Seed` and `10·size ≤ p^t` inputs are what the amplified gate error and the chosen amplification depth
`t` provide.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_ROADMAP.md`, `ACC_THEOREM_MAP.md`,
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ErrorCalibration

/-- **Per-gate error (proved): cancel the seed relation.**  From the averaging bound `cardS·E ≤ cardI·k`, the seed
relation `pt·k = cardS`, and `cardI = twoN` (with `k > 0`), the fixed-seed per-gate error satisfies `pt·E ≤ twoN`. -/
theorem per_gate_error (cardS cardI E k pt twoN : ℕ) (hk : 0 < k)
    (hgood : cardS * E ≤ cardI * k) (hseed : pt * k = cardS) (hI : cardI = twoN) :
    pt * E ≤ twoN := by
  subst cardI
  subst cardS
  have hgood' : (pt * E) * k ≤ twoN * k := by
    rw [show (pt * E) * k = (pt * k) * E by ring]
    exact hgood
  exact Nat.le_of_mul_le_mul_right hgood' hk

/-- **Error calibration (proved): `10·size ≤ p^t` makes the circuit error `< 2^n/10`.**  From the per-gate bound
`pt·E ≤ twoN` and the amplification calibration `10·size ≤ pt`, the total circuit error `size·E` satisfies
`10·(size·E) ≤ twoN` — i.e. `size·E < twoN/10`. -/
theorem error_calibration (size E pt twoN : ℕ) (hpt : 10 * size ≤ pt) (hgate : pt * E ≤ twoN) :
    10 * (size * E) ≤ twoN := by
  calc 10 * (size * E) = (10 * size) * E := by ring
    _ ≤ pt * E := Nat.mul_le_mul_right E hpt
    _ ≤ twoN := hgate

/-- **The combined calibration (proved): averaging + seed relation + amplification depth ⇒ circuit error `< 2^n/10`.** -/
theorem circuit_error_below_tenth (cardS cardI E k pt twoN size : ℕ) (hk : 0 < k)
    (hgood : cardS * E ≤ cardI * k) (hseed : pt * k = cardS) (hI : cardI = twoN)
    (hpt : 10 * size ≤ pt) :
    10 * (size * E) ≤ twoN :=
  error_calibration size E pt twoN hpt (per_gate_error cardS cardI E k pt twoN hk hgood hseed hI)

end PallLean.Paper93.DeepMath.PathB.ACC0ErrorCalibration

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ErrorCalibration.per_gate_error
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ErrorCalibration.error_calibration
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ErrorCalibration.circuit_error_below_tenth
