import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHennieGeneral

/-!
# The blank-phase halt-time bound, and an honest account of the remaining bookkeeping

`HennieGeneral` proved the load-bearing dichotomy: a machine reading only `false` from time `t₀`
halts within `|State|` steps or never.  This file sharpens it to a **halt-time bound**
(`blank_suffix_halt_time`): a machine that reads only `false` from `t₀` and does halt, first-halts by
step `t₀ + |State|`.  So no run computes for more than `|State|` steps in a blank phase — the exact
"no computation in empty space" statement in its most usable form.

## Why the full `time ≤ poly(distinctTapes, |x|)` bound is not closed here

The remaining step is `maxHead ≤ (rightmost written cell) + |State|`, from which
`maxHead ≤ |x| + |State|·distinctTapes` and then (via `time_le`) the polynomial time bound follow.
The head-bound is *true* but its clean formalization runs into three genuine subtleties, which is
why it is stated here honestly rather than proved:

1. **Finite excursions vs. infinite suffixes.**  `blank_suffix_halt_time` is about a blank phase
   that lasts until halt.  A head that pushes past the frontier and then *returns* is a finite
   excursion, to which the infinite-suffix lemma does not directly apply; ruling out a long
   returning excursion needs the drift analysis below, not just the suffix lemma.

2. **Backward reasoning.**  Bounding `maxHead` is about *how the head got there* — a backward
   question — whereas `blank_suffix_halt_time` is forward.  Reaching a position `> frontier +
   |State|` forces a rightward-drifting state cycle (`δ > 0`), and that cycle, being confined to the
   semi-infinite blank region, never halts; establishing "the cycle stays past the frontier forever"
   requires an induction that must also rule out the cycle dipping back below the frontier
   mid-period.

3. **Frontier tracking.**  One must define the rightmost-written cell as a function of time, prove
   it is non-decreasing except through writes, and count that each extension is a distinct tape.

Each is a real definitional/inductive obligation; together they are a multi-hundred-line
formalization.  Rather than commit a hand-waved or `sorry`-laden version, this file provides the
sharp usable lemma and records the obligation precisely.  The verdict is unchanged: settling it
would only confirm that `distinctRows` is polynomially equivalent to time (content-free).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This file proves no SAT lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.HennieHaltTime

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.HennieGeneral (blank_suffix_halts_fast)

variable {M : Machine}

/-- **The blank-phase halt-time bound.**  If a machine reads only `false` from time `t₀` and it does
halt (first at time `T ≥ t₀`), then it first-halts by step `t₀ + |State|`: no run computes for more
than `|State|` steps in a blank phase. -/
theorem blank_suffix_halt_time (c : Cfg M) (t0 T : ℕ) (ht0 : t0 ≤ T)
    (hread : ∀ k, M.halt (run M (t0 + k) c).st = false →
        (run M (t0 + k) c).tp.getD (run M (t0 + k) c).hd false = false)
    (hhalt : M.halt (run M T c).st = true)
    (hfirst : ∀ j, j < T → M.halt (run M j c).st = false) :
    T ≤ t0 + Fintype.card M.State := by
  rcases blank_suffix_halts_fast c t0 hread with ⟨k, hk, hhk⟩ | hnever
  · by_contra hgt
    push_neg at hgt
    have hlt : t0 + k < T := by omega
    rw [hfirst (t0 + k) hlt] at hhk
    simp at hhk
  · exfalso
    have hf := hnever (T - t0)
    rw [show t0 + (T - t0) = T from by omega] at hf
    rw [hf] at hhalt
    simp at hhalt

end PallLean.Paper93.DeepMath.PathB.HennieHaltTime
