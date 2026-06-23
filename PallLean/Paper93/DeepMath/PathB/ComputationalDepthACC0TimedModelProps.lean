import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TimedEnumeration

/-!
# Structural properties of the timed model: monotonicity and soundness (Williams machine model, rung 1d) (PROVED)

Two genuine facts about the concrete `evaln`-based timed enumeration (`ACC0TimedEnumeration.timedEnum`),
relating it to larger budgets and to the true (unbounded) computation — the foundations any time-hierarchy
argument rests on:

  `timedEnum_accept_mono` — acceptance is **monotone** in the step budget: if program `e` accepts `n`
  within `bound n` steps and `bound ≤ bound'`, it accepts within `bound' n` steps (more time only helps).
  `timedEnum_sound` — bounded acceptance is **sound**: if `e` accepts `n` within `bound n` steps then the
  true (unbounded) computation of `e` on `n` outputs `1`.

These come directly from Mathlib's `evaln_mono` (`k₁ ≤ k₂ → x ∈ evaln k₁ c n → x ∈ evaln k₂ c n`) and
`evaln_sound` (`x ∈ evaln k c n → x ∈ c.eval n`).  Monotonicity is exactly the "more budget never loses an
accept" fact, and soundness ties the step-bounded model to the partial-recursive semantics — both needed
to relate `TIME(bound)` and `TIME(bigbound)` once an efficient simulator is available.

## What is proved (clean axioms, no `sorry`)

* `timedEnum_accept_mono` — acceptance monotone in the budget.
* `timedEnum_sound` — bounded acceptance ⇒ true acceptance.

## Honest scope

Structural properties of the model.  The Williams **time** hierarchy still needs the efficient universal
simulator (`evaln` overhead `≤ bigbound`) to place the diagonal in the slightly-larger class — the deep
machine-model gap, Williams-strength, **not** built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0TimedModelProps

open Nat.Partrec Nat.Partrec.Code
open PallLean.Paper93.DeepMath.PathB.ACC0TimedEnumeration (timedEnum)

/-- **Acceptance is monotone in the step budget (proved).**  More time never loses an accept. -/
theorem timedEnum_accept_mono (bound bound' : ℕ → ℕ) (h : ∀ n, bound n ≤ bound' n) (e n : ℕ)
    (hacc : timedEnum bound e n = true) : timedEnum bound' e n = true := by
  unfold timedEnum at hacc ⊢
  rw [decide_eq_true_eq] at hacc ⊢
  exact evaln_mono (h n) hacc

/-- **Bounded acceptance is sound (proved).**  If program `e` accepts `n` within `bound n` steps, the true
(unbounded) computation of `e` on `n` outputs `1`. -/
theorem timedEnum_sound (bound : ℕ → ℕ) (e n : ℕ) (hacc : timedEnum bound e n = true) :
    (1 : ℕ) ∈ (Denumerable.ofNat Code e).eval n := by
  unfold timedEnum at hacc
  rw [decide_eq_true_eq] at hacc
  exact evaln_sound hacc

/-!
**Rung 1d proved.**  The timed model is acceptance-monotone in the budget and sound w.r.t. the true
computation — the structural foundations relating `TIME(bound)` to larger budgets and to the
partial-recursive semantics.  The efficient universal simulator (the diagonal within a *slightly larger*
budget) remains the deep machine-model gap.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0TimedModelProps

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TimedModelProps.timedEnum_accept_mono
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0TimedModelProps.timedEnum_sound
