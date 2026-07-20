import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingSpliceInduction

/-!
# Reset-free machines: leftward crossings land at `b`

The three-way splice was obstructed only by the reset move disturbing the leftward-crossing landing
(`step_exit_head`: land at `b` *or* `0`).  This file introduces the reset-free predicate and proves
that under it the landing is always `b`, removing the obstruction.

* `ResetFree` — the transition never emits a reset move (`Move = 3`); i.e. every move is left/right/stay.
  This is the standard left/right Turing-machine geometry (reset was added to `ComposableMachine` only
  for composability and adds no language-deciding power).
* `leftward_lands_at_b` — for a reset-free machine, a step taking the head from `> b` to `≤ b` lands it
  at exactly `b`, **regardless of the cell read**.

The read-independence is the point: `x_L` and `x_R` differ on the right, but a reset-free leftward
crossing lands at `b` for both, so their landings coincide and the splice's `SpliceSynced` alignment
survives the phase transition.  With rightward crossings already clean (`step_entry_head`: always
`b+1`), the crossing geometry is fully aligned for reset-free machines.

## Scope

This removes the geometric obstruction for reset-free machines.  The three-way splice induction
proper (assembling `splice_track_right`/`_left` under this geometry), the concrete palindrome family,
and the `Ω(n)`-cut summation remain.  This file does **not** claim the `Ω(n²)` bound, which — even
finished — is an unconditional *restricted* result (`crossingCount ≤ time` caps the technique at
polynomial; one-tape P `=` P) not bearing on `SAT ∉ P`.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- A machine is **reset-free** if its transition never emits the reset move (`Move = 3`): every move
is left, right, or stay — the standard left/right Turing-machine geometry. -/
def ResetFree (M : Machine) : Prop := ∀ s bit, (M.δ s bit).2.2 ≠ 3

/-- **Leftward crossings land at `b`.**  For a reset-free machine, a step taking the head from `> b`
to `≤ b` lands it at exactly `b`, independent of the cell read — so references differing on the right
still land together at a leftward crossing. -/
theorem leftward_lands_at_b (M : Machine) (hrf : ResetFree M) (b : ℕ) (c : Cfg M)
    (h1 : b < c.hd) (h2 : (step M c).hd ≤ b) : (step M c).hd = b := by
  by_cases hh : M.halt c.st = true
  · rw [step_of_halted M hh] at h2; omega
  · have hh1 : M.halt c.st = false := by simpa using hh
    have hstep : (step M c).hd = moveHead c.hd (M.δ c.st (c.tp.getD c.hd false)).2.2 := by
      rw [step_eq_of_not_halted M hh1]
    rw [hstep] at h2 ⊢
    have hmvne : (M.δ c.st (c.tp.getD c.hd false)).2.2 ≠ 3 := hrf c.st (c.tp.getD c.hd false)
    revert h2 hmvne
    generalize (M.δ c.st (c.tp.getD c.hd false)).2.2 = mv
    intro hmvne h2
    fin_cases mv <;> simp_all [moveHead] <;> omega

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
