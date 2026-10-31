import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingGluing
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingGluingLeft

/-!
# The splice: phase-tracking building blocks

The palindrome fooling's splice runs a *mixed* computation `z` (left tape from `x_L`, right tape from
`x_R`) and shows it follows `x_R` on right phases and `x_L` on left phases.  The two phase-tracking
steps are clean combinations of the run-level lemmas from both sides.

* `splice_track_right` — through a right phase (head `> b`), `z` tracks the right-reference on the
  right (`run_local_right`) while its left tape stays frozen (`run_left_frozen`).
* `splice_track_left` — through a left phase (head `≤ b`), `z` tracks the left-reference on the left
  (`run_local_left`) while its right tape stays frozen (`run_right_frozen`).

Together: on a right phase `z` matches `x_R` and preserves its left half; on a left phase `z` matches
`x_L` and preserves its right half.  That is exactly the alternation the splice needs.

## What still remains (NOT here)

The full splice assembles these into a **three-way crossing-indexed induction**: track `z, x_L, x_R`
at their respective `k`-th crossings, using `splice_track_right`/`_left` for `z`'s phases and the
hypothesis `crossing-sequence(x_L) = crossing-sequence(x_R)` to keep the entry states aligned across
the alternation (so `z`'s exit state, `= x_R`'s, equals `x_L`'s, re-aligning `z` with `x_L` for the
next left phase).  From that, `z` accepts iff the references do — the fooling contradiction.  That
three-way induction, the concrete palindrome family, and the `Ω(n)`-cut summation are the remaining
work; this file does **not** claim the `Ω(n²)` bound.

Ceiling unchanged: even finished, an unconditional *restricted* result (`crossingCount ≤ time` caps
the technique at polynomial; one-tape P `=` P), not `SAT ∉ P`.

Nothing here proves `P ≠ NP`, SAT hardness, or a lower bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

/-- **Right-phase tracking.**  If `z` and the right-reference share state and head and agree on cells
`> b`, and `z`'s head stays `> b` for `d` steps, then after the phase they still share state and head
and agree on `> b`, and `z`'s tape `≤ b` is unchanged. -/
theorem splice_track_right (M : Machine) (b : ℕ) (z xR : Cfg M) (d : ℕ)
    (hst : z.st = xR.st) (hhd : z.hd = xR.hd)
    (hagreeR : ∀ p, b < p → z.tp.getD p false = xR.tp.getD p false)
    (hphase : ∀ j, j < d → b < (run M j z).hd) :
    (run M d z).st = (run M d xR).st ∧ (run M d z).hd = (run M d xR).hd ∧
      (∀ p, b < p → (run M d z).tp.getD p false = (run M d xR).tp.getD p false) ∧
      (∀ p, p ≤ b → (run M d z).tp.getD p false = z.tp.getD p false) := by
  obtain ⟨hs, hh, hr⟩ := run_local_right M b z xR d hst hhd hagreeR hphase
  exact ⟨hs, hh, hr, fun p hp => run_left_frozen M b z d hphase p hp⟩

/-- **Left-phase tracking.**  If `z` and the left-reference share state and head and agree on cells
`≤ b`, and `z`'s head stays `≤ b` for `d` steps, then after the phase they still share state and head
and agree on `≤ b`, and `z`'s tape `> b` is unchanged. -/
theorem splice_track_left (M : Machine) (b : ℕ) (z xL : Cfg M) (d : ℕ)
    (hst : z.st = xL.st) (hhd : z.hd = xL.hd)
    (hagreeL : ∀ p, p ≤ b → z.tp.getD p false = xL.tp.getD p false)
    (hphase : ∀ j, j < d → (run M j z).hd ≤ b) :
    (run M d z).st = (run M d xL).st ∧ (run M d z).hd = (run M d xL).hd ∧
      (∀ p, p ≤ b → (run M d z).tp.getD p false = (run M d xL).tp.getD p false) ∧
      (∀ p, b < p → (run M d z).tp.getD p false = z.tp.getD p false) := by
  obtain ⟨hs, hh, hl⟩ := run_local_left M b z xL d hst hhd hagreeL hphase
  exact ⟨hs, hh, hl, fun p hp => run_right_frozen M b z d hphase p hp⟩

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
