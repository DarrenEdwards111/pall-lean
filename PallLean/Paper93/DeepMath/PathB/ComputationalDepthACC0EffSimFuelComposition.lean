import Mathlib

/-!
# Efficient-simulation build, rung 5a: `evaln` fuel composition (cost-model machinery) (PROVED)

Toward discharging the terminal `DiagRuntimePolyBounded` wall, the core machinery Mathlib lacks is a
**fuel cost model** for `evaln`.  This file proves the first genuine pieces — how the fuel budget composes
across the non-iterating `Code` constructors `comp` and `pair`, read off `evaln`'s recursion equations.

A crucial structural fact surfaces: `evaln (k+1) c n` carries a `guard (n ≤ k)` (the input-budget check,
matching `evaln_bound : x ∈ evaln k c n → n < k`).  So the **same** fuel `k+1` suffices for a composite as
for its parts, *provided `n ≤ k`*:

  `evaln_comp_fuel` — `n ≤ k`, `evaln (k+1) cg n = some w`, `evaln (k+1) cf w = some v`
    ⇒ `evaln (k+1) (comp cf cg) n = some v`.
  `evaln_pair_fuel` — `n ≤ k`, `evaln (k+1) cf n = some a`, `evaln (k+1) cg n = some b`
    ⇒ `evaln (k+1) (pair cf cg) n = some (Nat.pair a b)`.

**Consequence:** for any code built only from `comp`/`pair` over base constructors (no `prec`/`rfind'`
iteration), one *uniform* fuel `k+1` (with `k ≥ n` and large enough for the sub-evaluations) computes the
whole code — the non-iterating fragment has benign (input-linear) fuel.  Only `prec`/`rfind'` (iteration)
make fuel grow with the computation; bounding *those* is the remaining cost-model content.

## What is proved (clean axioms, no `sorry`)

* `evaln_comp_fuel`, `evaln_pair_fuel` — fuel composition for `comp` and `pair`.

## Honest scope

The non-iterating fuel-composition rules (the cost model's compositional core).  The `prec`/`rfind'`
iteration-fuel bounds, and assembling them into an explicit efficient universal simulator (Hennie–Stearns),
remain the deep gap.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EffSimFuelComposition

open Nat.Partrec Nat.Partrec.Code

/-- **Fuel composition for `comp` (proved).**  With `n ≤ k`, the same fuel `k+1` that evaluates `cg` at `n`
and `cf` at the result evaluates `comp cf cg` at `n`. -/
theorem evaln_comp_fuel {k : ℕ} {cf cg : Code} {n w v : ℕ} (hn : n ≤ k)
    (hg : Code.evaln (k + 1) cg n = some w) (hf : Code.evaln (k + 1) cf w = some v) :
    Code.evaln (k + 1) (Code.comp cf cg) n = some v := by
  simp [Code.evaln.eq_7, hn, hg, hf]

/-- **Fuel composition for `pair` (proved).**  With `n ≤ k`, the same fuel `k+1` evaluating `cf` and `cg`
at `n` evaluates `pair cf cg` at `n`. -/
theorem evaln_pair_fuel {k : ℕ} {cf cg : Code} {n a b : ℕ} (hn : n ≤ k)
    (hf : Code.evaln (k + 1) cf n = some a) (hg : Code.evaln (k + 1) cg n = some b) :
    Code.evaln (k + 1) (Code.pair cf cg) n = some (Nat.pair a b) := by
  simp [Code.evaln.eq_6, hn, hf, hg]

/-!
**Rung 5a proved.**  Fuel composes uniformly across `comp`/`pair` given the input-budget guard `n ≤ k` —
the non-iterating fragment of `evaln` has benign fuel.  The `prec`/`rfind'` iteration-fuel bounds and the
efficient universal simulator remain the deep gap.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0EffSimFuelComposition

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimFuelComposition.evaln_comp_fuel
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimFuelComposition.evaln_pair_fuel
