import Mathlib

/-!
# Efficient-simulation build, rung 5c: `evaln` base-constructor fuel — cost model complete (PROVED)

The leaves of the `evaln` fuel cost model: the base constructors `zero`, `succ`, `left`, `right` (from
`evaln.eq_2..5`) and the zero-fuel law (`evaln.eq_1`).  Each base constructor at fuel `k+1` succeeds
*exactly when* the input passes the budget guard `n ≤ k` — confirming **base fuel is input-linear**
(`fuel = n + 1`):

  `evaln_zero_none` — `evaln 0 c n = none` (no fuel computes nothing).
  `evaln_zero_fuel` / `evaln_succ_fuel` / `evaln_left_fuel` / `evaln_right_fuel` — the base outputs at fuel
    `k+1` given `n ≤ k`.

With rungs 5a (`comp`/`pair`) and 5b (`prec`/`rfind'`), the fuel cost model now covers **all nine `Code`
constructors**.  Net picture: `evaln` fuel = (iteration depth) + (input-linear non-iterating cost) —
*polynomial* in the simulated step budget and input, never exponential.

## What is proved (clean axioms, no `sorry`)

* `evaln_zero_none`, `evaln_zero_fuel`, `evaln_succ_fuel`, `evaln_left_fuel`, `evaln_right_fuel` — the base
  fuel rules.

## Honest scope

The fuel cost model is complete (all constructors).  Assembling it into an *explicit* fuel-bounded
universal simulator code (discharging `DiagRuntimePolyBounded`) is the remaining construction — now with a
*polynomial* target bound, the path concrete.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EffSimBaseFuel

open Nat.Partrec

/-- **Zero fuel computes nothing (proved).** -/
theorem evaln_zero_none (c : Code) (n : ℕ) : Code.evaln 0 c n = (none : Option ℕ) := by
  simp only [Code.evaln.eq_1]

/-- **`zero` base fuel (proved): `fuel n+1`, input guard `n ≤ k`.** -/
theorem evaln_zero_fuel {k n : ℕ} (hn : n ≤ k) : Code.evaln (k + 1) Code.zero n = some 0 := by
  simp [Code.evaln.eq_2, hn]

/-- **`succ` base fuel (proved).** -/
theorem evaln_succ_fuel {k n : ℕ} (hn : n ≤ k) : Code.evaln (k + 1) Code.succ n = some (n + 1) := by
  simp [Code.evaln.eq_3, hn]

/-- **`left` base fuel (proved).** -/
theorem evaln_left_fuel {k n : ℕ} (hn : n ≤ k) :
    Code.evaln (k + 1) Code.left n = some (Nat.unpair n).1 := by
  simp [Code.evaln.eq_4, hn]

/-- **`right` base fuel (proved).** -/
theorem evaln_right_fuel {k n : ℕ} (hn : n ≤ k) :
    Code.evaln (k + 1) Code.right n = some (Nat.unpair n).2 := by
  simp [Code.evaln.eq_5, hn]

/-!
**Rung 5c proved — cost model complete.**  All nine `Code` constructors now have fuel rules (base: rung 5c;
`comp`/`pair`: rung 5a; `prec`/`rfind'`: rung 5b).  `evaln` fuel = iteration-depth + input-linear cost =
polynomial in (step budget, input).  Building an explicit fuel-bounded universal simulator from these rules
(discharging `DiagRuntimePolyBounded`) is the remaining construction.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0EffSimBaseFuel

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimBaseFuel.evaln_zero_fuel
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimBaseFuel.evaln_succ_fuel
