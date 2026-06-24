import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimCodeFuel

/-!
# Kleene interpreter project — `runtimeOf` is depth-like, not size-like (PROVED)

A plan-revising realization, verified concretely.  `runtimeOf` (the `evaln`-fuel cost model) is the time
measure of the timed hierarchy.  My runtime recurrences are **`max`-based**, not sum-based:
`runtimeOf_comp_le` bounds `comp` by `max(n+1, runtimeOf cg n, runtimeOf cf w)` — the *larger* of the
subcode costs, not their sum.  So `runtimeOf` grows with the recursion **depth and the values handled**, not
with the (possibly exponential) computation-tree **size**.

Consequence for the universal interpreter: the structural simulator has **polynomial `runtimeOf`** — the
exponential naive-`evaln` *tree* (repeated subcodes) inflates actual time but **not** the `evaln`-fuel.  So
the runtime target needs **no memoization**; the explicit structural interpreter's fuel is bounded by the
value bound (`config_encode_le`) and the recursion depth, via the `max`-recurrences already proved.

This file verifies the principle on a concrete family where the computation *structure* grows without bound
yet the fuel stays constant:

  `compPow m` — the `m`-fold self-composition `comp id (comp id (… id))`.
  `eval_compPow` — it computes the identity (`= n`).
  `runtimeOf_compPow_le` — `runtimeOf (compPow m) n ≤ n + 1` **for every `m`** — fuel is constant in the
    nesting depth `m`, i.e. independent of code size.

## What is proved (clean axioms, no `sorry`)

* `compPow`, `eval_compPow`, `halts_compPow`, `runtimeOf_compPow_le`.

## Honest scope

A verified realization that revises the build plan: the runtime target is reachable via the `max`-recurrences
+ value bound, without a memoized DP.  The explicit structural interpreter `Code` (course-of-values on
`encode c` for the *realization* of the recursion) is still the remaining construction; only its runtime
*analysis* is now known to be straightforward.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.KleeneRuntimeDepth

open Nat.Partrec
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntime (runtimeOf runtimeOf_isSome halts_iff_dom)
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimCodeFuel (runtimeOf_id_le)
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntimeRecurrence (runtimeOf_comp_le)

/-- `m`-fold self-composition of `Code.id`: a code whose *structure* grows with `m`. -/
def compPow : ℕ → Code
  | 0 => Code.id
  | m + 1 => Code.comp Code.id (compPow m)

/-- **`compPow m` computes the identity (proved).** -/
theorem eval_compPow (m n : ℕ) : (compPow m).eval n = Part.some n := by
  induction m with
  | zero => simp [compPow, Code.eval]
  | succ m ih =>
    have e : (compPow (m + 1)).eval n = ((compPow m).eval n).bind Code.id.eval := rfl
    rw [e, ih]; simp [Code.eval]

theorem halts_compPow (m n : ℕ) : ∃ k, (Code.evaln k (compPow m) n).isSome := by
  rw [halts_iff_dom, eval_compPow]; trivial

theorem halts_left (n : ℕ) : ∃ k, (Code.evaln k Code.left n).isSome := by
  rw [halts_iff_dom, show Code.left.eval n = Part.some (Nat.unpair n).1 from by simp [Code.eval]]; trivial

theorem halts_right (n : ℕ) : ∃ k, (Code.evaln k Code.right n).isSome := by
  rw [halts_iff_dom, show Code.right.eval n = Part.some (Nat.unpair n).2 from by simp [Code.eval]]; trivial

/-- **`runtimeOf` is constant in the nesting depth (proved): `runtimeOf (compPow m) n ≤ n + 1` for all `m`.**
The computation tree of `compPow m` grows with `m`, yet the `evaln`-fuel stays `≤ n + 1` — confirming
`runtimeOf` is depth/value-like, not size-like. -/
theorem runtimeOf_compPow_le (m n : ℕ) (h : ∃ k, (Code.evaln k (compPow m) n).isSome) :
    runtimeOf (compPow m) n h ≤ n + 1 := by
  induction m generalizing n with
  | zero => exact runtimeOf_id_le n (halts_left n) (halts_right n) h
  | succ m ih =>
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (runtimeOf_isSome (compPow m) n (halts_compPow m n))
    have hwn : w = n := by
      have := Code.evaln_sound hw; rw [eval_compPow] at this; exact Part.mem_some_iff.mp this
    have hid : ∃ k, (Code.evaln k Code.id w).isSome := by
      rw [halts_iff_dom, show Code.id.eval w = Part.some w from by simp [Code.eval]]; trivial
    have hb := runtimeOf_comp_le (cf := Code.id) (cg := compPow m) (n := n) (w := w)
      (halts_compPow m n) hw hid h
    have h1 := ih n (halts_compPow m n)
    have h2 := runtimeOf_id_le w (halts_left w) (halts_right w) hid
    show runtimeOf (Code.comp Code.id (compPow m)) n h ≤ n + 1
    omega

/-!
**Realization verified.**  `runtimeOf` is depth/value-bounded, not tree-size-bounded: `compPow m` has fuel
`≤ n+1` for every nesting depth `m`.  So the structural universal interpreter has polynomial `runtimeOf` via
the `max`-recurrences + value bound — no memoization needed for the runtime target.  The explicit
interpreter `Code` remains the construction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.KleeneRuntimeDepth

#print axioms PallLean.Paper93.DeepMath.PathB.KleeneRuntimeDepth.runtimeOf_compPow_le
