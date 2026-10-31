import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimRuntime
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimExplicitBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimDominating
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimWall
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimEfficientCode
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimFuelComposition
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimIterationFuel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimBaseFuel

/-!
# Efficient-simulation overhead build — machine-checked manifest

The user-committed build attacking Williams' deep algorithmic-half ingredient: turning the *crude*
unconditional time hierarchy (opaque `bigbound`) into the *efficient* one.  Built on Mathlib's
`Nat.Partrec.Code.evaln`.  All rungs clean (`[propext, Classical.choice, Quot.sound]`, no `sorry`).

## Part A — the structural reduction (rungs 1–4b)

1. **Runtime cost-measure** — `runtimeOf` + spec (minimality, **stability**, halts↔dom).
2. **Explicit `bigbound`** — `timed_hierarchy_explicit`: `TIME(bound) ⊊ TIME(diagRuntime)` (named minimal
   runtime, not a `choose`).
3. **Domination reduction** — `efficient_hierarchy_of_dominating`: via stability, `TIME(bound) ⊊ TIME(g)`
   for **any** `g ≥ diagRuntime`.
4. **Gap isolated** — `efficient_poly_hierarchy_of_overhead`: the hypothesis `DiagRuntimePolyBounded`
   (poly-bounded diagonal runtime) yields the efficient poly-overhead hierarchy.
4b. **Intrinsic form** — `efficient_hierarchy_of_efficient_code`: *any* efficiently-running decider for the
   diagonal ⇒ `TIME(bound) ⊊ TIME(g)`.

## Part B — the `evaln` fuel cost model (rungs 5a–5c, the machinery Mathlib lacks)

5a. **`comp`/`pair` fuel** — `evaln_comp_fuel`, `evaln_pair_fuel`: same fuel composes given the guard `n ≤ k`.
5b. **`prec`/`rfind'` fuel** — `evaln_prec_*`, `evaln_rfind'_*`: iteration recurses at fuel **`k`**
    (decremented by one per step).
5c. **base fuel** — `evaln_zero/succ/left/right_fuel` (+ `evaln_zero_none`): input-linear leaves.

**Net result (all nine constructors):** the fuel rules compose, and iteration decrements fuel by one per
step (so iteration contributes linearly).  **Caveat (honest):** the guard `n ≤ k` holds at *every* node,
including inner nodes where `n` is an *intermediate value* — so `evaln` fuel is `≥` the largest
intermediate value, not merely the original input.  Thus the fuel is *(iteration depth) + (max intermediate
value)*, and whether that is **polynomial** for a universal simulator depends on the intermediate values
staying polynomial.  There is reason to expect this (`evaln`'s own guards bound the *simulated*
computation's values to `≤ bound e`), but it is **not proved here** — it is precisely the delicate
value-bookkeeping of Hennie–Stearns.  So efficiency is *plausible but not established*; the cost model is a
genuine foundation, not a proof of polynomial overhead.

## The remaining gap

Assemble the fuel rules into an **explicit fuel-bounded universal simulator code** (a `Code` interpreting
`evaln`, the Kleene universal machine — Mathlib's `exists_code` is *opaque*) **and** prove its intermediate
values stay polynomial, discharging `DiagRuntimePolyBounded`.  Both are substantial (the value-bookkeeping
is the Hennie–Stearns core), **not** built.  Then the efficient hierarchy feeds the Williams `NEXP ⊄ ACC⁰`
interface.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EffSimManifest

-- Part A: structural reduction
#check @ACC0EffSimRuntime.runtimeOf
#check @ACC0EffSimRuntime.evaln_runtimeOf_stable
#check @ACC0EffSimExplicitBound.timed_hierarchy_explicit
#check @ACC0EffSimDominating.efficient_hierarchy_of_dominating
#check @ACC0EffSimWall.efficient_poly_hierarchy_of_overhead
#check @ACC0EffSimEfficientCode.efficient_hierarchy_of_efficient_code

-- Part B: evaln fuel cost model (all 9 constructors)
#check @ACC0EffSimFuelComposition.evaln_comp_fuel
#check @ACC0EffSimFuelComposition.evaln_pair_fuel
#check @ACC0EffSimIterationFuel.evaln_prec_zero_fuel
#check @ACC0EffSimIterationFuel.evaln_prec_succ_fuel
#check @ACC0EffSimIterationFuel.evaln_rfind'_found_fuel
#check @ACC0EffSimIterationFuel.evaln_rfind'_step_fuel
#check @ACC0EffSimBaseFuel.evaln_zero_fuel
#check @ACC0EffSimBaseFuel.evaln_succ_fuel
#check @ACC0EffSimBaseFuel.evaln_left_fuel
#check @ACC0EffSimBaseFuel.evaln_right_fuel

-- Clean-axiom confirmation
#print axioms ACC0EffSimDominating.efficient_hierarchy_of_dominating
#print axioms ACC0EffSimEfficientCode.efficient_hierarchy_of_efficient_code
#print axioms ACC0EffSimIterationFuel.evaln_prec_succ_fuel

end PallLean.Paper93.DeepMath.PathB.ACC0EffSimManifest
