import Mathlib

/-!
# Efficient-simulation build, rung 1: a runtime cost-measure for `Code.evaln` (PROVED)

This begins the **efficient-simulation overhead** build — the deep ingredient that turns the *crude*
unconditional time hierarchy (`ACC0TimedHierarchyUnconditional`, with an opaque `bigbound`) into the
Williams *efficient* hierarchy (`bigbound` only slightly larger than `bound`).  The opaque `bigbound` there
was a `Classical.choose`'d halting budget; to control it we first need a **cost measure**: the exact number
of `evaln` fuel-steps a computation needs.

  `runtimeOf c n h` — the least fuel `k` with `(evaln k c n).isSome`, for a halting computation
  (`h : ∃ k, (evaln k c n).isSome`).

with its specification:

  `runtimeOf_isSome` — `evaln` succeeds at the runtime budget.
  `le_runtimeOf` — minimality: any succeeding budget is `≥ runtimeOf`.
  `lt_runtimeOf_isNone` — below the runtime budget, `evaln` has not yet halted.
  `evaln_runtimeOf_stable` — at or above `runtimeOf`, `evaln` is constant (`evaln_mono`).
  `halts_iff_dom` — the runtime is defined exactly when the true computation `c.eval n` is defined.

## Build plan (the efficient-simulation overhead, rungs)

1. **runtime cost-measure** (this file): `runtimeOf` + specification.
2. structure/runtime relation: bound `runtimeOf` by the `Code` structure and input.
3. universal simulation: a single `Code`/`TM2` simulating `evaln` with controlled overhead.
4. efficiency: `bigbound ≤ f(bound)` with `f` only slightly super-linear (the Hennie–Stearns ingredient).
5. cash-out: the efficient hierarchy → the Williams `NEXP ⊄ ACC⁰` interface.

## What is proved (clean axioms, no `sorry`)

* `runtimeOf` + `runtimeOf_isSome` / `le_runtimeOf` / `lt_runtimeOf_isNone` / `evaln_runtimeOf_stable` /
  `halts_iff_dom` — the cost measure and its specification.

## Honest scope

The cost *measure* (rung 1).  Bounding it (rungs 2–4, the actual efficient-simulation overhead) is the deep
Williams-strength content, **not** built here.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntime

open Nat.Partrec Nat.Partrec.Code

/-- **Runtime cost-measure**: the least `evaln` fuel making the computation halt. -/
noncomputable def runtimeOf (c : Code) (n : ℕ) (h : ∃ k, (Code.evaln k c n).isSome) : ℕ :=
  Nat.find h

/-- **`evaln` succeeds at the runtime budget (proved).** -/
theorem runtimeOf_isSome (c : Code) (n : ℕ) (h : ∃ k, (Code.evaln k c n).isSome) :
    (Code.evaln (runtimeOf c n h) c n).isSome :=
  Nat.find_spec h

/-- **Minimality (proved): any halting budget is `≥ runtimeOf`.** -/
theorem le_runtimeOf (c : Code) (n : ℕ) (h : ∃ k, (Code.evaln k c n).isSome) {k : ℕ}
    (hk : (Code.evaln k c n).isSome) : runtimeOf c n h ≤ k :=
  Nat.find_le hk

/-- **Below the runtime budget the computation has not halted (proved).** -/
theorem lt_runtimeOf_isNone (c : Code) (n : ℕ) (h : ∃ k, (Code.evaln k c n).isSome) {k : ℕ}
    (hk : k < runtimeOf c n h) : ¬ (Code.evaln k c n).isSome :=
  Nat.find_min h hk

/-- **Stability (proved): at or above `runtimeOf`, `evaln` is constant.** -/
theorem evaln_runtimeOf_stable (c : Code) (n : ℕ) (h : ∃ k, (Code.evaln k c n).isSome) {k : ℕ}
    (hk : runtimeOf c n h ≤ k) : Code.evaln k c n = Code.evaln (runtimeOf c n h) c n := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (runtimeOf_isSome c n h)
  rw [hv]
  exact evaln_mono hk hv

/-- **The runtime is defined exactly when the true computation halts (proved).** -/
theorem halts_iff_dom (c : Code) (n : ℕ) :
    (∃ k, (Code.evaln k c n).isSome) ↔ (c.eval n).Dom := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
    exact (evaln_sound hv).fst
  · intro hd
    obtain ⟨k, hk⟩ := evaln_complete.mp ⟨hd, rfl⟩
    exact ⟨k, hk ▸ rfl⟩

/-!
**Rung 1 proved.**  `runtimeOf` is a genuine cost measure on `Code.evaln`: minimal halting budget, with
`evaln` succeeding there and stable above.  The next rungs bound `runtimeOf` (by structure, then via a
universal simulator with controlled overhead) — the deep efficient-simulation content.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntime

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntime.runtimeOf_isSome
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntime.evaln_runtimeOf_stable
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntime.halts_iff_dom
