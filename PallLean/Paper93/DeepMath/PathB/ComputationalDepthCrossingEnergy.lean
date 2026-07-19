import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingMeasureTest

/-!
# A nonlinear crossing statistic: quadratic energy

To test whether the peak/total sandwich rules out nonlinear crossing statistics, define the
quadratic energy of the crossing-load vector

`energy = ∑_{b<S} crossingCount(b)^2`.

The checked result is deliberately limited:

* total load is at most energy (integer loads satisfy `x ≤ x²`);
* energy is at most peak times total (`x² ≤ max·x` pointwise);
* consequently energy is at most `T·total`, since every fixed boundary is crossed at most `T` times;
* and energy is at most `S·T²`.

Thus quadratic energy is a genuine nonlinear concentration statistic lying between total load and
peak-weighted total load.  These inequalities neither prove it hard for SAT nor kill it: they expose
the exact further work required.  In particular, this file makes no space-invariance, simulation-
robustness, or superpolynomial lower-bound claim.
-/

namespace PallLean.Paper93.DeepMath.PathB.CrossingComplexity

open PallLean.Paper93.DeepMath.PathB.ComposableMachine

variable {M : Machine}

/-- Sum of squared crossing loads over boundaries `[0,S)`. -/
noncomputable def crossingEnergy (M : Machine) (c : Cfg M) (S T : ℕ) : ℕ :=
  ∑ b ∈ Finset.range S, (crossingCount M c b T) ^ 2

private theorem self_le_square (x : ℕ) : x ≤ x ^ 2 := by
  cases x with
  | zero => simp
  | succ x =>
      have hx : 1 ≤ x + 1 := by omega
      nlinarith

/-- Integer crossing load is bounded by its quadratic energy. -/
theorem sumCrossings_le_crossingEnergy (c : Cfg M) (S T : ℕ) :
    sumCrossings M c S T ≤ crossingEnergy M c S T := by
  unfold sumCrossings crossingEnergy
  exact Finset.sum_le_sum fun b _ => self_le_square (crossingCount M c b T)

/-- Quadratic energy is bounded by peak load times total load. -/
theorem crossingEnergy_le_max_mul_sum (c : Cfg M) (S T : ℕ) :
    crossingEnergy M c S T ≤ maxCrossing M c S T * sumCrossings M c S T := by
  unfold crossingEnergy sumCrossings
  calc
    ∑ b ∈ Finset.range S, (crossingCount M c b T) ^ 2
        ≤ ∑ b ∈ Finset.range S,
            maxCrossing M c S T * crossingCount M c b T := by
          apply Finset.sum_le_sum
          intro b hb
          have hle := crossingCount_le_maxCrossing c (Finset.mem_range.mp hb) T
          simpa [pow_two, mul_comm] using
            Nat.mul_le_mul_right (crossingCount M c b T) hle
    _ = maxCrossing M c S T *
          (∑ b ∈ Finset.range S, crossingCount M c b T) := by
          rw [Finset.mul_sum]

/-- Every fixed-boundary peak is bounded by the elapsed step count. -/
theorem maxCrossing_le_time (c : Cfg M) (S T : ℕ) :
    maxCrossing M c S T ≤ T := by
  unfold maxCrossing
  apply Finset.sup_le
  intro b _
  exact crossingCount_le_time c b T

/-- Energy is at most elapsed time times total crossing load. -/
theorem crossingEnergy_le_time_mul_sum (c : Cfg M) (S T : ℕ) :
    crossingEnergy M c S T ≤ T * sumCrossings M c S T :=
  (crossingEnergy_le_max_mul_sum c S T).trans
    (Nat.mul_le_mul_right (sumCrossings M c S T) (maxCrossing_le_time c S T))

/-- Coarse sound bound: `S` boundaries, each with load at most `T`, have energy at most `S·T²`. -/
theorem crossingEnergy_le_space_mul_time_sq (c : Cfg M) (S T : ℕ) :
    crossingEnergy M c S T ≤ S * T ^ 2 := by
  unfold crossingEnergy
  calc
    ∑ b ∈ Finset.range S, (crossingCount M c b T) ^ 2
        ≤ ∑ _b ∈ Finset.range S, T ^ 2 := by
          apply Finset.sum_le_sum
          intro b _
          exact Nat.pow_le_pow_left (crossingCount_le_time c b T) 2
    _ = S * T ^ 2 := by simp

#print axioms sumCrossings_le_crossingEnergy
#print axioms crossingEnergy_le_max_mul_sum
#print axioms crossingEnergy_le_time_mul_sum
#print axioms crossingEnergy_le_space_mul_time_sq

end PallLean.Paper93.DeepMath.PathB.CrossingComplexity
