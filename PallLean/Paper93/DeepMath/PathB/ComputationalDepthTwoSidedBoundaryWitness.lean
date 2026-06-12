import PallLean.Paper93.DeepMath.PathB.ComputationalDepthContinuationObserver
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLowBoundaryFromStreaming

/-!
# A two-sided boundary witness: both engines fire on one function (the honest synthesis)

The session built two engines:

* the **lower-bound engine** (God-Move): a hard instance forces *high* boundary under a decomposition class;
* the **algorithm engine** (Williams direction): a *low*-boundary decomposition gives a fast DP and feeds the
  Williams bridge.

They use **opposite** boundary conditions — which is why they cannot be naively composed.  This file makes
their relationship concrete and honest: **one function witnesses both**, in *different* decomposition classes.
EQUALITY has

* **high** boundary in the single-cut faithful-observer class (`≥ n`, `equality_continuation_forces_boundary`),
  and
* **low** boundary in the streaming class (`= 1`, giving a `LowBoundaryInstance` whose DP beats brute force).

Both are *proved*.  So "high boundary somewhere" and "low boundary elsewhere (fast algorithm)" coexist on a
single function — this is the decomposition gap (`equality_decomposition_gap`) read as the bridge between the
two engines.

## What is proved (clean axioms, no `sorry`)

`equality_two_sided` — EQUALITY simultaneously:
1. forces every faithful **single-cut** observer to boundary `≥ n` (the lower-bound engine's input), and
2. admits a **streaming** `LowBoundaryInstance` whose DP strictly beats brute force (the algorithm engine's
   input).

## Honest status — this is NOT a separation

The two-sidedness is exactly why neither engine alone separates:

* EQUALITY's *high* boundary is **single-cut only** — provably insufficient (`equality_decomposition_gap`:
  another decomposition is cheap), so the lower-bound engine does not bite.
* EQUALITY's *low* boundary makes it **easy** — so the algorithm engine's "fast SAT" is unsurprising and the
  Williams bridge has nothing hard to diagonalise against.

A genuine separation needs a function that is high-boundary in **every** admissible decomposition (so no cheap
algorithm exists) — the open all-decompositions quantifier (`= CookLevinFrontierHyp`).  Neither engine, nor
their combination here, supplies that.  The value is a clean, proved statement of how the engines relate on a
concrete witness, with the open core left exactly where it is.
-/

namespace PallLean.Paper93.DeepMath.PathB.TwoSidedWitness

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.ContinuationObserver
open PallLean.Paper93.DeepMath.PathB.ObserverAlgorithmic
open PallLean.Paper93.DeepMath.PathB.LowBoundaryFromStreaming

/-- **The two-sided witness (proved).**  The EQUALITY family witnesses *both* engines:

1. **Lower-bound engine** — every faithful single-cut observer of `n`-bit EQUALITY has boundary `≥ n`;
2. **Algorithm engine** — `2k`-bit EQUALITY has a streaming `LowBoundaryInstance` whose DP over its `2`
   boundary states strictly beats brute force.

The same function is high-boundary in one decomposition class and low-boundary in another — the engines are
complementary, not composable.  (This is *not* a separation; see the module docstring.) -/
theorem equality_two_sided (n k : ℕ) (hk : 1 ≤ k) :
    (∀ O : BranchingObserver (Fin n → Bool), Faithful O (eqDec n) → n ≤ O.entropy)
    ∧ dpSatTime (equalityLowBoundaryInstance k hk).stages
          (equalityLowBoundaryInstance k hk).boundary
        < bruteForceTime (equalityLowBoundaryInstance k hk).n :=
  ⟨fun O hf => equality_continuation_forces_boundary n O hf,
   equality_dp_beats_bruteforce k hk⟩

end PallLean.Paper93.DeepMath.PathB.TwoSidedWitness

#print axioms PallLean.Paper93.DeepMath.PathB.TwoSidedWitness.equality_two_sided
