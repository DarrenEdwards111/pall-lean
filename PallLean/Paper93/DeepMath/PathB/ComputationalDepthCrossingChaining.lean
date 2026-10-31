import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingGluing

/-!
# Crossing-indexed chaining: the cycle-entry alignment (continued)

The cut-and-paste determinism chains `(right-excursion, left-excursion)` cycles.  For the chaining to
close, each re-entry into the right region must land the two computations in a matching state at a
matching head position.  The head position is *forced*: a rightward crossing can only happen by a
right-move from cell `b` to cell `b+1` (reset goes to `0 ≤ b`; no other move increases the head past
`b`).  So every entry is at head `b+1`, and the two computations align in head position at every
re-entry automatically — only the *state* alignment needs the crossing-sequence hypothesis.

* `step_entry_head` — a step taking the head from `≤ b` to `> b` lands it at exactly `b+1`.
* `entry_frozen_and_head` — at the first entry time `ts` (head `≤ b` throughout `[0,ts)`, `> b` at
  `ts`): the head is `b+1`, and the tape right of `b` is unchanged from the start (frozen until
  entry, via `run_right_frozen`).

Applied to two computations with equal initial right tapes: at first entry both have head `b+1` and
equal right tapes, so if their first crossing states agree (crossing-sequence hypothesis),
`run_local_right` runs the first right-excursion in lockstep.  This is one cycle of the chain.

## What still remains (NOT done here)

The full determinism `equal crossing sequence + equal right tape ⇒ equal final right tape` iterates
this cycle: define the `k`-th entry/exit times recursively (`Nat.find` of the next crossing), and
induct on the crossing index `k`, using `run_local_right` for each right-excursion, `run_right_frozen`
across each left-excursion, and `entry_frozen_and_head` / `step_entry_head` to re-establish the
head-`b+1` + equal-right-tape invariant at each re-entry (state equality from the crossing sequence).
That recursive-time induction is the remaining assembly; it is **not** carried out here, and the
palindrome `Ω(n²)` fooling/counting on top of it is further work.

Standing ceiling unchanged: even finished this is an unconditional *restricted* bound
(`crossingCount ≤ time` caps the technique at polynomial; one-tape P `=` P), not `SAT ∉ P`.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- **Entry geometry.**  A single step taking the head from `≤ b` to `> b` lands it at exactly `b+1`:
the only move that increases the head is a right-move, from `b` to `b+1`. -/
theorem step_entry_head (M : Machine) (b : ℕ) (c : Cfg M)
    (h1 : c.hd ≤ b) (h2 : b < (step M c).hd) : (step M c).hd = b + 1 := by
  by_cases hh : M.halt c.st = true
  · rw [step_of_halted M hh] at h2; omega
  · have hh1 : M.halt c.st = false := by simpa using hh
    have hstep : (step M c).hd = moveHead c.hd (M.δ c.st (c.tp.getD c.hd false)).2.2 := by
      rw [step_eq_of_not_halted M hh1]
    rw [hstep] at h2 ⊢
    unfold moveHead at h2 ⊢
    split_ifs at h2 ⊢ <;> omega

/-- **First-entry alignment.**  If the head stays at `≤ b` for the first `ts` steps and exceeds `b`
at step `ts`, then at time `ts` the head is exactly `b+1` and the tape right of `b` is unchanged from
the start. -/
theorem entry_frozen_and_head (M : Machine) (b : ℕ) (c : Cfg M) (ts : ℕ)
    (hstart : c.hd ≤ b)
    (hbefore : ∀ j, j < ts → (run M j c).hd ≤ b)
    (hcross : b < (run M ts c).hd) :
    (run M ts c).hd = b + 1 ∧
      ∀ p, b < p → (run M ts c).tp.getD p false = c.tp.getD p false := by
  have hts : 1 ≤ ts := by
    rcases Nat.eq_zero_or_pos ts with h0 | hpos
    · rw [h0, run_zero] at hcross; omega
    · exact hpos
  refine ⟨?_, fun p hp => run_right_frozen M b c ts hbefore p hp⟩
  have hprev : (run M (ts - 1) c).hd ≤ b := hbefore (ts - 1) (by omega)
  have hrun : run M ts c = step M (run M (ts - 1) c) := by
    conv_lhs => rw [show ts = (ts - 1) + 1 by omega]
    rw [run_succ]
  rw [hrun] at hcross ⊢
  exact step_entry_head M b (run M (ts - 1) c) hprev hcross

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
