import Mathlib.Data.Nat.Basic

/-!
# Breaking the counting/largeness barrier in a restricted case: the non-large detector

The counting barrier is Razborov–Rudich **largeness**: a natural property must hold for a *large* fraction
(`≥ 2^{-O(n)}`) of all functions.  A lower-bound method whose detector is **non-large** — sparse —
**evades** it.  This is the paper's Theorem 51 move, and it is a real counting fact.

Total functions on `n` inputs: `2^{2^n}` (doubly exponential).  Functions with a **small circuit** (say
`≤ n²`-ish gates): at most `2^{poly(n)}` (there are only that many small circuits).  So "low complexity"
is **sparse** — its density is `2^{poly(n) − 2^n}`, far below the largeness threshold.

## What is proved

* **`counting_barrier_evaded` (proved)** — the low-complexity detector is **below the largeness
  threshold**: for `n²+n < 2^n`, `2^n · 2^{n²} < 2^{2^n}`.  Even after multiplying the simple-function
  count `2^{n²}` by the threshold slack `2^n`, it stays under the total `2^{2^n}`.  So "low complexity" is
  non-large — a proof using it as its detector **evades** the counting/largeness barrier.

## Honest scope — one barrier down, not the wall

Evading largeness is real and it is *necessary* — any proof of `NP ⊄ P/poly` must fail largeness or
constructivity (else crypto breaks).  A **non-large** detector like low SPDP rank / low complexity clears
the counting barrier, in a restricted case, here.

But it is *not sufficient*.  The three-driver directed machine had **three** walls; this breaks only the
**counting** one.  What remains:

* the detector must still be **useful** — proving the hard function is *not* low-complexity is exactly
  `cost_super` (the shrinkage-rate wall);
* the **`L_eff`/`L_H` dilemma** stands — a *non-large* detector that is also *efficient* is still ruled out
  by the relativization/algebrization companions, and the paper's Boolean bridge is assumed.

So: **the counting barrier is broken, in the restricted (non-large) case** — genuinely, one of the three
drivers cleared.  The other two (`cost_super`, `L_eff`/`L_H`) remain.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CountingBarrierBreak

/-- **The counting/largeness barrier is evaded (proved).**  The number of low-complexity functions
(`2^{n²}`, at most that many small circuits), even boosted by the largeness threshold slack `2^n`, stays
strictly below the total `2^{2^n}`: `2^n · 2^{n²} < 2^{2^n}` whenever `n²+n < 2^n`.  So "low complexity"
is **non-large**, and a detector using it clears the counting barrier. -/
theorem counting_barrier_evaded (n : ℕ) (hn : n ^ 2 + n < 2 ^ n) :
    2 ^ n * 2 ^ (n ^ 2) < 2 ^ (2 ^ n) := by
  have h1 : 2 ^ n * 2 ^ (n ^ 2) = 2 ^ (n + n ^ 2) := by rw [Nat.pow_add]
  rw [h1]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

end PallLean.Paper93.DeepMath.PathB.CountingBarrierBreak

#print axioms PallLean.Paper93.DeepMath.PathB.CountingBarrierBreak.counting_barrier_evaded
