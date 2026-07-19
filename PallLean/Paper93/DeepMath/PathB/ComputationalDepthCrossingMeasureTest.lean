import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingSpaceBarrier

/-!
# Peak/total crossing sandwich

This file combines the two elementary inequalities relating peak and total crossing load.  It does
not claim a no-go theorem for all crossing-derived measures.

## The two natural crossing measures, sandwiched

* `sumCrossings` — the *total* crossing activity (a space-invariant proxy: total head movement).
* `maxCrossing` — the *peak* crossing count (space-sensitive).

`crossing_measure_sandwich` proves `maxCrossing ≤ sumCrossings ≤ S · maxCrossing`.  Thus their ratio,
when defined, is between `1` and `S`; it is not necessarily exactly `S`.  The inequalities leave room
for nonlinear statistics between peak and total.

## Reversals are not settled here

No reversal theorem is stated: stay-put and reset moves require explicit treatment, and elapsed time
cannot be bounded by reversals without further hypotheses.

## Exact scope

The sandwich is bookkeeping, not a quantified dichotomy or impossibility result.  The companion
quadratic-energy file tests one nonlinear statistic rigorously.

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

/-- Peak and total are sandwiched within a factor bounded by the number of considered boundaries.
No universal claim about other crossing statistics follows from this alone. -/
theorem crossing_measure_sandwich (c : Cfg M) (S T : ℕ) :
    maxCrossing M c S T ≤ sumCrossings M c S T ∧
      sumCrossings M c S T ≤ S * maxCrossing M c S T :=
  ⟨maxCrossing_le_sumCrossings c S T, sumCrossings_le_space_mul_maxCrossing c S T⟩

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
