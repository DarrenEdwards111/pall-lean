import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingLocality

/-!
# Run-level excursion gluing (toward the palindrome `Ω(n²)` bound)

`CrossingLocality` gave the two *step*-level facts.  This file lifts them to whole excursions — the
run-level gluing lemmas that the cut-and-paste chaining is built from.

* `run_local_right` — **right-excursion lockstep.**  Two configurations that share state and head and
  agree on cells right of `b` stay synchronized (same state, head, right tape) for as many steps as
  the head stays strictly right of `b`.  (Iterated `step_local_right`.)
* `run_right_frozen` — **left-excursion freeze.**  While the head stays at `≤ b`, the tape right of
  `b` is unchanged after any number of steps.  (Iterated `step_right_frozen`.)

These are exactly the two motions the cut-and-paste alternates: a right-excursion evolves both
computations identically (`run_local_right`), and the intervening left-excursion — of *different*
length in the two computations — leaves the right tape untouched (`run_right_frozen`), so at the next
re-entry the right tapes still agree and, if the crossing sequences agree, the entry states agree, so
the next right-excursion is again in lockstep.

## What remains for the full palindrome `Ω(n²)` (NOT done here)

Completing the bound needs, on top of these two lemmas:

1. **Crossing-indexed chaining.**  Define the `k`-th crossing time of each computation and induct on
   `k` (aligning by crossing index, not time), using the two lemmas above to carry right-tape
   agreement across each (right-excursion, left-excursion) cycle — yielding the determinism
   `equal crossing sequence + equal right tape ⇒ equal final right tape`.
2. **Palindrome fooling.**  Distinct middle-halves force distinct crossing sequences at a center
   boundary (else the spliced computation misclassifies some `u·u'ᴿ`).
3. **Counting over `Ω(n)` boundaries.**  `crossing_info_capacity` turns `2^Ω(n)` distinct crossing
   sequences into `Ω(n)` crossings at each of `Ω(n)` middle boundaries, summing to `Ω(n²)` time.

Only step (0) — the run-level gluing — is completed here.  Steps 1–3 are the remaining substantial
work; this file does not claim the `Ω(n²)` bound.  And per the standing ceiling, even the finished
bound is an unconditional *restricted* result (`crossingCount ≤ time` caps the technique at
polynomial; one-tape P `=` P) that does not bear on `SAT ∉ P`.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- **Right-excursion lockstep.**  If two configurations share state and head and agree on cells
right of `b`, and the head of the first stays strictly right of `b` for the first `k` steps, then
after `k` steps the two still share state and head and agree right of `b`. -/
theorem run_local_right (M : Machine) (b : ℕ) (c₁ c₂ : Cfg M) (k : ℕ)
    (hst : c₁.st = c₂.st) (hhd : c₁.hd = c₂.hd)
    (hagree : ∀ p, b < p → c₁.tp.getD p false = c₂.tp.getD p false)
    (hstay : ∀ j, j < k → b < (run M j c₁).hd) :
    (run M k c₁).st = (run M k c₂).st ∧ (run M k c₁).hd = (run M k c₂).hd ∧
      (∀ p, b < p → (run M k c₁).tp.getD p false = (run M k c₂).tp.getD p false) := by
  revert hstay
  induction k with
  | zero => intro _; exact ⟨hst, hhd, hagree⟩
  | succ k ih =>
    intro hstay
    obtain ⟨ihst, ihhd, ihag⟩ := ih (fun j hj => hstay j (by omega))
    rw [run_succ, run_succ]
    exact step_local_right M b (run M k c₁) (run M k c₂) ihst ihhd (hstay k (by omega)) ihag

/-- **Left-excursion freeze.**  If the head stays at `≤ b` for the first `k` steps, then the tape
right of `b` is unchanged after `k` steps. -/
theorem run_right_frozen (M : Machine) (b : ℕ) (c : Cfg M) (k : ℕ)
    (hstay : ∀ j, j < k → (run M j c).hd ≤ b) (p : ℕ) (hp : b < p) :
    (run M k c).tp.getD p false = c.tp.getD p false := by
  revert hstay
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hstay
    rw [run_succ, step_right_frozen M b (run M k c) (hstay k (by omega)) p hp]
    exact ih (fun j hj => hstay j (by omega))

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
