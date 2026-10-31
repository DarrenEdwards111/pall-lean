import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingComplexity

/-!
# Peak/total crossing averaging

This file records the elementary averaging relation between total and peak boundary-crossing load.
It does **not** prove that adding space lowers the peak, or that crossing-sequence methods have a
particular lower-bound ceiling.

* `sumCrossings M c S T` = total crossings summed over the `S` boundaries `[0,S)`.
* `maxCrossing M c S T` = the peak crossing count over those boundaries.
* `sumCrossings_le_space_mul_maxCrossing`: `sumCrossings ≤ S · maxCrossing`.
  Equivalently, the peak is at least the average crossing load.

## Exact scope

The theorem is a lower bound on the peak, not an upper bound: it gives
`maxCrossing ≥ sumCrossings / S`.  Moreover, this machine model has a reset-to-zero move, so one step
may cross many boundaries and `sumCrossings` is not automatically equal to elapsed time.  Proving a
genuine space-dilution result would require a semantics-preserving simulation or a quantified theorem
over a defined class of layouts; neither is asserted here.

## What remains open

The inequality alone does not rule out nonlinear or multiscale statistics of the crossing-load
distribution.  Such candidates require separate definitions and proofs.

Nothing here proves a separation or a superpolynomial bound.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

variable {M : Machine}

/-- Total crossings summed over the `S` boundaries `[0,S)`. -/
noncomputable def sumCrossings (M : Machine) (c : Cfg M) (S T : ℕ) : ℕ :=
  ∑ b ∈ Finset.range S, crossingCount M c b T

/-- The peak crossing count over the `S` boundaries `[0,S)`. -/
noncomputable def maxCrossing (M : Machine) (c : Cfg M) (S T : ℕ) : ℕ :=
  (Finset.range S).sup (fun b => crossingCount M c b T)

/-- Every boundary's crossing count is at most the peak. -/
theorem crossingCount_le_maxCrossing (c : Cfg M) {b S : ℕ} (hb : b < S) (T : ℕ) :
    crossingCount M c b T ≤ maxCrossing M c S T := by
  unfold maxCrossing
  exact Finset.le_sup (f := fun b => crossingCount M c b T) (Finset.mem_range.mpr hb)

/-- The total crossing activity is at most the number of considered boundaries times the peak.
Equivalently, the peak is at least the average load. -/
theorem sumCrossings_le_space_mul_maxCrossing (c : Cfg M) (S T : ℕ) :
    sumCrossings M c S T ≤ S * maxCrossing M c S T := by
  unfold sumCrossings
  calc ∑ b ∈ Finset.range S, crossingCount M c b T
      ≤ (Finset.range S).card • maxCrossing M c S T :=
        Finset.sum_le_card_nsmul _ _ _
          (fun b hb => crossingCount_le_maxCrossing c (Finset.mem_range.mp hb) T)
    _ = S * maxCrossing M c S T := by rw [Finset.card_range, smul_eq_mul]

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
