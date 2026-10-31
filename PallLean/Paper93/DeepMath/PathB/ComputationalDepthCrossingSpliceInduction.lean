import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingSplice

/-!
# The three-way splice invariant, and the reset obstruction (honest)

Assembling the splice phase-tracking steps into a three-way induction surfaces a genuine, model-specific
obstruction that this file pins down formally.

* `SpliceSynced` — the intended invariant: the mixed computation `z`, the left-reference `x_L`, and the
  right-reference `x_R` share state and head, with `z`'s left tape `= x_L`'s and `z`'s right tape
  `= x_R`'s.
* `step_exit_head` — a leftward crossing (head `> b` to `≤ b`) lands at **either `b` (a left-move) or
  `0` (a reset)**.

## The obstruction

The splice alternates: `z` tracks `x_R` on a right phase (`splice_track_right`) — landing, at the
leftward crossing that ends it, exactly where `x_R` lands (lockstep, same right tape) — then must track
`x_L` on the next left phase.  For that it needs `z`'s landing head to equal `x_L`'s landing head at
`x_L`'s corresponding crossing.  But by `step_exit_head` a leftward crossing lands at `b` *or* `0`
depending on the cell read, and that cell is on the **right** (`> b`), where `x_L` and `x_R` differ.
So `x_R` may reset (land `0`) while `x_L` left-moves (land `b`): `z` follows `x_R` to `0`, `x_L` is at
`b`, and the alignment `SpliceSynced` needs is broken.

In a reset-free (standard left/right) machine this cannot happen: every leftward crossing is a
left-move landing at `b`, regardless of the read, so `x_L` and `x_R` always land together and the
three-way induction goes through.  Rightward crossings are already clean in *this* model
(`step_entry_head`: always `b+1`); it is only the leftward-crossing landing that the reset move
disturbs.

So the honest status: the three-way splice induction holds for the **reset-free** geometry, and
completing it requires either restricting to reset-free machines (the standard TM model) or a
reset-elimination simulation.  That, the palindrome family, and the `Ω(n)`-cut summation are the
remaining work; this file does **not** claim the `Ω(n²)` bound.

Ceiling unchanged: even finished, an unconditional *restricted* result (`crossingCount ≤ time` caps the
technique at polynomial; one-tape P `=` P), not `SAT ∉ P`.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- The three-way splice invariant: `z` (mixed), `x_L` (left-reference), `x_R` (right-reference) share
state and head, with `z`'s tape `≤ b` matching `x_L` and its tape `> b` matching `x_R`. -/
def SpliceSynced (M : Machine) (b : ℕ) (z xL xR : Cfg M) : Prop :=
  z.st = xL.st ∧ z.st = xR.st ∧ z.hd = xL.hd ∧ z.hd = xR.hd ∧
    (∀ p, p ≤ b → z.tp.getD p false = xL.tp.getD p false) ∧
    (∀ p, b < p → z.tp.getD p false = xR.tp.getD p false)

/-- **Exit geometry.**  A step taking the head from `> b` to `≤ b` lands it at exactly `b` (a
left-move, forced when the head was at `b+1`) or at `0` (a reset).  Which one depends on the cell read
— and that cell is on the right, so `x_L` and `x_R` (differing there) can land differently: the reset
obstruction to the three-way splice. -/
theorem step_exit_head (M : Machine) (b : ℕ) (c : Cfg M)
    (h1 : b < c.hd) (h2 : (step M c).hd ≤ b) : (step M c).hd = b ∨ (step M c).hd = 0 := by
  by_cases hh : M.halt c.st = true
  · rw [step_of_halted M hh] at h2; omega
  · have hh1 : M.halt c.st = false := by simpa using hh
    have hstep : (step M c).hd = moveHead c.hd (M.δ c.st (c.tp.getD c.hd false)).2.2 := by
      rw [step_eq_of_not_halted M hh1]
    rw [hstep] at h2 ⊢
    unfold moveHead at h2 ⊢
    split_ifs at h2 ⊢ <;> omega

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
