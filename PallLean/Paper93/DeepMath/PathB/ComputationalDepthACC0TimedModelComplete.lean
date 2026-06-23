import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TimedModelProps

/-!
# The timed model captures the true semantics, and the budget bounds the input (rung 1e) (PROVED)

Completing the metatheory of the concrete `evaln`-based timed enumeration: pairing soundness
(`ACC0TimedModelProps.timedEnum_sound`) with **completeness**, and recording the **input-budget bound**.

  `timedEnum_input_bound` — acceptance requires `n < bound n`: a program cannot accept input `n` within
  `bound n` steps unless the budget exceeds the input (via `evaln_bound`).
  `timedEnum_captures_eval` — the union over all budgets of the timed accept-sets is **exactly** the true
  (unbounded) accept-set: `(∃ k, evaln k (decode e) n = some 1) ↔ 1 ∈ (decode e).eval n` (via
  `evaln_complete`).

Together with soundness, `timedEnum_captures_eval` says the step-counted model is a faithful resource
refinement of the partial-recursive semantics — exactly the object an efficient simulator would compress.

## What is proved (clean axioms, no `sorry`)

* `timedEnum_input_bound` — acceptance ⇒ `n < bound n`.
* `timedEnum_captures_eval` — `⋃_k TIME(k)`-acceptance `=` true acceptance.

## Honest scope

The model's soundness/completeness metatheory.  The Williams **time** hierarchy still needs the efficient
universal simulator (`evaln` overhead `≤ bigbound`) to place the diagonal in a *slightly larger* class —
the deep machine-model gap, Williams-strength, **not** built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TimedModelComplete

open Nat.Partrec Nat.Partrec.Code
open PallLean.Paper93.DeepMath.PathB.ACC0TimedEnumeration (timedEnum)

/-- **The budget bounds the input (proved): acceptance requires `n < bound n`.** -/
theorem timedEnum_input_bound (bound : ℕ → ℕ) (e n : ℕ) (hacc : timedEnum bound e n = true) :
    n < bound n := by
  unfold timedEnum at hacc
  rw [decide_eq_true_eq] at hacc
  exact evaln_bound hacc

/-- **The timed model captures the true semantics (proved): `⋃_k`-acceptance `=` true acceptance.**  Some
budget accepts iff the unbounded computation outputs `1`. -/
theorem timedEnum_captures_eval (e n : ℕ) :
    (∃ k, Code.evaln k (Denumerable.ofNat Code e) n = some 1)
      ↔ (1 : ℕ) ∈ (Denumerable.ofNat Code e).eval n :=
  evaln_complete.symm

/-!
**Rung 1e proved.**  Acceptance forces `n < bound n`, and the union of the timed accept-sets is exactly the
partial-recursive accept-set (soundness + completeness).  The efficient universal simulator (the diagonal
within a *slightly larger* budget) remains the deep machine-model gap.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TimedModelComplete

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TimedModelComplete.timedEnum_input_bound
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TimedModelComplete.timedEnum_captures_eval
