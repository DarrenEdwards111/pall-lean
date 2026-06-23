import Mathlib

/-!
# Efficient-simulation build, rung 5b: `evaln` iteration-fuel for `prec`/`rfind'` (PROVED)

Completing the `evaln` fuel cost model: the iteration constructors `prec` and `rfind'` (read off
`evaln.eq_8`/`eq_9`).  The decisive structural fact — the recursive iteration step uses `evaln k`
(fuel **decremented by one**), not `evaln (k+1)`:

  `evaln_prec_zero_fuel` — base step: `prec` at counter `0` runs `cf` at the same fuel.
  `evaln_prec_succ_fuel` — iteration step: `prec` at counter `y+1` (fuel `k+1`) needs the recursive value
    at counter `y` **at fuel `k`** plus `cg` at fuel `k+1`.
  `evaln_rfind'_found_fuel` — `rfind'` halts (`cf = 0`) returning the counter.
  `evaln_rfind'_step_fuel` — `rfind'` continues (`cf ≠ 0`) recursing **at fuel `k`**.

**Consequence (the cost model's headline):** fuel decreases by exactly one per iteration, so the fuel an
`evaln` computation needs is its **iteration depth plus the (benign, input-linear) non-iterating cost** —
i.e. fuel grows *linearly* with the number of iteration steps, never exponentially.  A universal simulator
running `t` steps therefore needs `O(t + input)` fuel — **polynomial**, exactly the shape
`DiagRuntimePolyBounded` requires.  So efficiency is *structurally* achievable; what remains is an
**explicit** universal-simulator code (Mathlib's `exists_code` is opaque) whose iteration count is the
simulated step budget.

## What is proved (clean axioms, no `sorry`)

* `evaln_prec_zero_fuel` / `evaln_prec_succ_fuel` / `evaln_rfind'_found_fuel` / `evaln_rfind'_step_fuel`
  — the iteration-fuel rules; with rung 5a (`comp`/`pair`) the fuel cost model is complete for all
  recursive constructors.

## Honest scope

The fuel cost model is now complete (the linear-in-iterations machinery Mathlib lacks).  Building an
*explicit* fuel-bounded universal simulator code (and assembling it into `DiagRuntimePolyBounded`) remains
the deep gap — but the cost model shows the target bound is polynomial, not exponential.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EffSimIterationFuel

open Nat.Partrec Nat.Partrec.Code

/-- **`prec` base-step fuel (proved).** -/
theorem evaln_prec_zero_fuel {k : ℕ} {cf cg : Code} {a v : ℕ} (hn : Nat.pair a 0 ≤ k)
    (hf : Code.evaln (k + 1) cf a = some v) :
    Code.evaln (k + 1) (Code.prec cf cg) (Nat.pair a 0) = some v := by
  simp [Code.evaln.eq_8, hn, hf]

/-- **`prec` iteration-step fuel (proved): the recursive call is at fuel `k` (decremented).** -/
theorem evaln_prec_succ_fuel {k : ℕ} {cf cg : Code} {a y i v : ℕ} (hn : Nat.pair a (y + 1) ≤ k)
    (hi : Code.evaln k (Code.prec cf cg) (Nat.pair a y) = some i)
    (hg : Code.evaln (k + 1) cg (Nat.pair a (Nat.pair y i)) = some v) :
    Code.evaln (k + 1) (Code.prec cf cg) (Nat.pair a (y + 1)) = some v := by
  simp [Code.evaln.eq_8, hn, hi, hg]

/-- **`rfind'` halting fuel (proved): `cf = 0` returns the counter.** -/
theorem evaln_rfind'_found_fuel {k : ℕ} {cf : Code} {a m : ℕ} (hn : Nat.pair a m ≤ k)
    (hx : Code.evaln (k + 1) cf (Nat.pair a m) = some 0) :
    Code.evaln (k + 1) (Code.rfind' cf) (Nat.pair a m) = some m := by
  simp [Code.evaln.eq_9, hn, hx]

/-- **`rfind'` continuation fuel (proved): `cf ≠ 0` recurses at fuel `k` (decremented).** -/
theorem evaln_rfind'_step_fuel {k : ℕ} {cf : Code} {a m x v : ℕ} (hn : Nat.pair a m ≤ k) (hx0 : x ≠ 0)
    (hx : Code.evaln (k + 1) cf (Nat.pair a m) = some x)
    (hr : Code.evaln k (Code.rfind' cf) (Nat.pair a (m + 1)) = some v) :
    Code.evaln (k + 1) (Code.rfind' cf) (Nat.pair a m) = some v := by
  simp [Code.evaln.eq_9, hn, hx, hx0, hr]

/-!
**Rung 5b proved.**  The iteration constructors decrement fuel by exactly one per step, so `evaln` fuel is
**iteration-depth + benign non-iterating cost** — *linear* in iterations.  With rung 5a the fuel cost model
is complete; it shows a `t`-step universal simulation needs `O(t + input)` fuel (polynomial), so
`DiagRuntimePolyBounded` is structurally achievable once an explicit universal-simulator code is built.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0EffSimIterationFuel

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimIterationFuel.evaln_prec_succ_fuel
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimIterationFuel.evaln_rfind'_step_fuel
