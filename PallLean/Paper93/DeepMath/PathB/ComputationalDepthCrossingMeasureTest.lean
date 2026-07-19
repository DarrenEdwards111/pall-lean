import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingSpaceBarrier

/-!
# Testing proposed measures against the crossing-for-space barrier

The barrier asks for a measure that is **space-invariant** (not diluted by more space) yet **strictly
below time** (not `≈ time`).  This file runs candidates through `sumCrossings_le_space_mul_maxCrossing`
and reports the verdict.

## The two natural crossing measures, sandwiched

* `sumCrossings` — the *total* crossing activity (a space-invariant proxy: total head movement).
* `maxCrossing` — the *peak* crossing count (space-sensitive).

`crossing_measure_sandwich` proves `maxCrossing ≤ sumCrossings ≤ S · maxCrossing`.  The two differ by
exactly a factor of the space `S`.  So within crossing-derived measures the space-invariant end
(`sumCrossings`) and the sub-time end (`maxCrossing`) are separated by space itself — there is no
crossing-derived measure that is simultaneously space-invariant and a genuine `time / poly` refinement.
`sumCrossings` is space-invariant but `≈ time` (content-free); `maxCrossing` is sub-time but `≤ time/S`
(diluted).  **Verdict: every crossing-derived measure fails — killed by the sandwich.**

## A non-crossing candidate: reversals

`reversals` (head direction changes) is the natural non-crossing candidate.  It does not escape:
each maximal monotone sweep crosses a boundary at most once, so `maxCrossing ≤ reversals + 1`, i.e.
`reversals ≥ maxCrossing`.  And dually `time ≤ (space) · (reversals + 1)` (time is the sum of sweep
lengths, each `≤` space, over `reversals + 1` sweeps) — the *same* space tradeoff as crossings.  So
`reversals` sits in `[time/space, time]` exactly like `maxCrossing`, diluted by the same mechanism.
**Verdict: reversals fails too** — it reduces to the crossing tradeoff.  (The reversal↔sweep
counting is stated here; only the crossing-derived sandwich is machine-checked.)

## The pattern

Every trace measure tried so far obeys a dichotomy: either it satisfies `time ≤ space · μ` (diluted:
`maxCrossing`, `distinctRows`, `reversals`, communication) or it is space-free `time ≤ poly(μ)` and
hence `≈ time` (content-free: `sumCrossings`, distinct-configs).  Escaping the barrier requires a
measure outside this dichotomy — a "crossing" cost space cannot flatten.  None is proposed here that
survives; the sandwich is the concrete no-go for the crossing family.

Nothing here proves a separation or a superpolynomial bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

variable {M : Machine}

/-- The peak crossing is at most the total crossing activity. -/
theorem maxCrossing_le_sumCrossings (c : Cfg M) (S T : ℕ) :
    maxCrossing M c S T ≤ sumCrossings M c S T := by
  unfold maxCrossing sumCrossings
  apply Finset.sup_le
  intro b hb
  exact Finset.single_le_sum (f := fun b => crossingCount M c b T) (fun i _ => Nat.zero_le _) hb

/-- **The crossing-measure test verdict.**  The space-invariant total and the sub-time peak are
sandwiched within a factor of the space `S`: `maxCrossing ≤ sumCrossings ≤ S · maxCrossing`.  So no
crossing-derived measure is both space-invariant and a genuine sub-time refinement — the invariant
end is `≈ time`, the sub-time end is diluted by `S`, and nothing lies strictly between. -/
theorem crossing_measure_sandwich (c : Cfg M) (S T : ℕ) :
    maxCrossing M c S T ≤ sumCrossings M c S T ∧
      sumCrossings M c S T ≤ S * maxCrossing M c S T :=
  ⟨maxCrossing_le_sumCrossings c S T, sumCrossings_le_space_mul_maxCrossing c S T⟩

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
