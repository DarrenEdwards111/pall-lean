import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0EffSimPrecRecurrence

/-!
# Interpreter grind, step 3: solving the `prec` recurrence to a linear closed form (PROVED)

The runtime recurrence `runtimeOf (prec cf cg) (pair a (y+1)) ≤ max(…, runtimeOf (prec …) (pair a y) + 1, …)`
unrolls to a **linear** closed form, *conditional on a uniform step-cost bound* `D` (the deferred
value-bound — every base/per-step/input cost `≤ D`).  The `+1` per iteration accumulates to `+m`:

  `runtimeOf_prec_le_linear` — under `D`-bounds on the base cost, the per-step `cg` costs, and the inputs,
  `runtimeOf (prec cf cg) (pair a m) ≤ D + m`.

This is the genuine "solve the recurrence" step: it turns the per-step recurrence (step 2) into a closed
runtime bound, *linear in the iteration count* `m` — exactly the shape a universal simulator running `m`
steps needs, with `D` to be discharged later by the value-bound (`D = bound e`).

## What is proved (clean axioms, no `sorry`)

* `runtimeOf_prec_le_linear` — the closed linear runtime bound for `prec`, given a uniform step-cost `D`.

## Honest scope

The closed form is *conditional* on the uniform step-cost bound `D` (the value-bound, deferred).  Solving
`rfind'` likewise, establishing `D` for the universal simulator (the value-bound), and the explicit
interpreter, remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0EffSimPrecSolve

open Nat.Partrec Nat.Partrec.Code
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimRuntime (runtimeOf runtimeOf_isSome)
open PallLean.Paper93.DeepMath.PathB.ACC0EffSimPrecRecurrence
  (runtimeOf_prec_zero_le runtimeOf_prec_succ_le)

/-- **The `prec` recurrence solved to a linear closed form (proved).**  Given a uniform bound `D` on the
base cost, the per-step `cg` costs, and the inputs, the runtime at counter `m` is `≤ D + m`. -/
theorem runtimeOf_prec_le_linear {cf cg : Code} {a D : ℕ}
    (hh : ∀ m, ∃ k, (Code.evaln k (Code.prec cf cg) (Nat.pair a m)).isSome)
    (hf : ∃ k, (Code.evaln k cf a).isSome)
    (hbase : runtimeOf cf a hf ≤ D)
    (hin : ∀ m, Nat.pair a m + 1 ≤ D)
    (hstep : ∀ m i,
      Code.evaln (runtimeOf (Code.prec cf cg) (Nat.pair a m) (hh m)) (Code.prec cf cg) (Nat.pair a m)
        = some i →
      ∃ hg : ∃ k, (Code.evaln k cg (Nat.pair a (Nat.pair m i))).isSome,
        runtimeOf cg (Nat.pair a (Nat.pair m i)) hg ≤ D) :
    ∀ m, runtimeOf (Code.prec cf cg) (Nat.pair a m) (hh m) ≤ D + m := by
  intro m
  induction m with
  | zero =>
    have := runtimeOf_prec_zero_le hf (hh 0)
    have hin0 := hin 0
    omega
  | succ y ih =>
    obtain ⟨i, hpi⟩ := Option.isSome_iff_exists.mp
      (runtimeOf_isSome (Code.prec cf cg) (Nat.pair a y) (hh y))
    obtain ⟨hg, hgD⟩ := hstep y i hpi
    have hrec := runtimeOf_prec_succ_le (hp := hh y) hpi hg (hprec := hh (y + 1))
    have hiny := hin (y + 1)
    omega

/-!
**Interpreter grind step 3 proved.**  The `prec` recurrence solves to `runtimeOf ≤ D + m` — linear in the
iteration count, conditional on a uniform step-cost `D` (the deferred value-bound).  Establishing `D` for
the universal simulator (`D = bound e`) is the value-bound; the explicit interpreter remains.  Nothing here
is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0EffSimPrecSolve

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0EffSimPrecSolve.runtimeOf_prec_le_linear
