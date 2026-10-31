import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimBaseFuel
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimRuntimeRecurrence

/-!
# Interpreter construction, step 1: concrete fuel bounds for real codes (PROVED)

First genuine step of the explicit-interpreter construction: bounding the `runtimeOf` of **actual** `Code`s
via the cost-model recurrences — validating the machinery end-to-end on concrete codes and starting the
interpreter's primitive library (the interpreter is assembled from such primitives).

  `runtimeOf_zero_le` / `succ` / `left` / `right` — base constructors have `runtimeOf ≤ n + 1`
    (input-linear: just the budget guard).
  `runtimeOf_id_le` — `Code.id = pair left right` has `runtimeOf ≤ n + 1`, via `runtimeOf_pair_le` over the
    base bounds.

These are the first concrete fuel bounds in the build: real codes, real `runtimeOf` bounds, computed by the
recurrences — proof that the cost model bounds actual code fuel.

## What is proved (clean axioms, no `sorry`)

* `runtimeOf_zero_le`, `runtimeOf_succ_le`, `runtimeOf_left_le`, `runtimeOf_right_le` — base fuel bounds.
* `runtimeOf_id_le` — `Code.id`'s fuel bound (first composite, via the `pair` recurrence).

## Honest scope

Concrete fuel bounds for base codes + `id` (interpreter primitives; machinery validated on real codes).
The full universal interpreter (Gödel-dispatch + `prec`-on-fuel) assembled from such primitives remains the
construction.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EffSimCodeFuel

open Nat.Partrec Nat.Partrec.Code
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntime (runtimeOf le_runtimeOf)
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimBaseFuel
  (evaln_zero_fuel evaln_succ_fuel evaln_left_fuel evaln_right_fuel)
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntimeRecurrence (runtimeOf_pair_le)

/-- **`zero` fuel bound (proved): `≤ n + 1`.** -/
theorem runtimeOf_zero_le (n : ℕ) (h : ∃ k, (Code.evaln k Code.zero n).isSome) :
    runtimeOf Code.zero n h ≤ n + 1 :=
  le_runtimeOf Code.zero n h (by rw [evaln_zero_fuel (le_refl n)]; rfl)

/-- **`succ` fuel bound (proved): `≤ n + 1`.** -/
theorem runtimeOf_succ_le (n : ℕ) (h : ∃ k, (Code.evaln k Code.succ n).isSome) :
    runtimeOf Code.succ n h ≤ n + 1 :=
  le_runtimeOf Code.succ n h (by rw [evaln_succ_fuel (le_refl n)]; rfl)

/-- **`left` fuel bound (proved): `≤ n + 1`.** -/
theorem runtimeOf_left_le (n : ℕ) (h : ∃ k, (Code.evaln k Code.left n).isSome) :
    runtimeOf Code.left n h ≤ n + 1 :=
  le_runtimeOf Code.left n h (by rw [evaln_left_fuel (le_refl n)]; rfl)

/-- **`right` fuel bound (proved): `≤ n + 1`.** -/
theorem runtimeOf_right_le (n : ℕ) (h : ∃ k, (Code.evaln k Code.right n).isSome) :
    runtimeOf Code.right n h ≤ n + 1 :=
  le_runtimeOf Code.right n h (by rw [evaln_right_fuel (le_refl n)]; rfl)

/-- **`Code.id` fuel bound (proved): `≤ n + 1`.**  `id = pair left right`; first composite fuel bound via
the `pair` recurrence over the base bounds. -/
theorem runtimeOf_id_le (n : ℕ)
    (hl : ∃ k, (Code.evaln k Code.left n).isSome) (hr : ∃ k, (Code.evaln k Code.right n).isSome)
    (hid : ∃ k, (Code.evaln k Code.id n).isSome) :
    runtimeOf Code.id n hid ≤ n + 1 := by
  show runtimeOf (Code.pair Code.left Code.right) n hid ≤ n + 1
  have hbound := runtimeOf_pair_le (cf := Code.left) (cg := Code.right) hl hr hid
  have hlb := runtimeOf_left_le n hl
  have hrb := runtimeOf_right_le n hr
  omega

/-!
**Interpreter construction step 1 proved.**  Concrete fuel bounds for base codes and `id` (`≤ n + 1`),
computed by the cost-model recurrences — the machinery works on real codes, and these are the interpreter's
first primitives.  The full universal interpreter assembled from such primitives remains the construction.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0EffSimCodeFuel

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimCodeFuel.runtimeOf_id_le
