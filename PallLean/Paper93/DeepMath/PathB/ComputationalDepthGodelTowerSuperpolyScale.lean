import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGodelTowerSpring

/-!
# Gödel-tower superpolynomial scale socket

This file separates the elementary exponential scale calculation from the
unresolved solver-capture theorem.  Once a fanout-stable load satisfies the
restricted tower recurrence `2 * load i + 1 ≤ load (i+1)`, it dominates
`2^k`.  Hence at any level `k` for which `n^C < 2^k`, that load exceeds the
degree-`C` polynomial budget at input length `n`.

The structure `SolverCaptureDoubling` is deliberately an input to the
theorems.  Constructing it from an arbitrary polynomial-time SAT solver is the
open P-vs-NP-strength step; it is not installed as an axiom here.
-/

namespace PallLean.Paper93.DeepMath.PathB.GodelTowerSuperpolyScale

/-- The exact missing solver-capture payload: a positive initial semantic load
and a fanout-stable doubling step at every Gödel level. -/
structure SolverCaptureDoubling (load : Nat → Nat) : Prop where
  base : 1 ≤ load 0
  doubling : ∀ i, 2 * load i + 1 ≤ load (i + 1)

/-- Explicitly named socket.  Proving this proposition for the load extracted
from every polynomial SAT solver is the unresolved theorem. -/
def solver_capture_doubling (load : Nat → Nat) : Prop :=
  SolverCaptureDoubling load

/-- The restricted recurrence supplies the exponential tower bound. -/
theorem pow_two_le_load {load : Nat → Nat}
    (capture : SolverCaptureDoubling load) :
    ∀ k, 2 ^ k ≤ load k := by
  intro k
  induction k with
  | zero => simpa using capture.base
  | succ k ih =>
      have hmul : 2 * 2 ^ k ≤ 2 * load k := Nat.mul_le_mul_left 2 ih
      calc
        2 ^ (k + 1) = 2 * 2 ^ k := by simp [pow_succ, Nat.mul_comm]
        _ ≤ 2 * load k + 1 := by omega
        _ ≤ load (k + 1) := capture.doubling k

/-- A quantitative scale witness: level `k` already outruns degree `C` at
input length `n`. -/
def SuperpolyScaleWitness (n k C : Nat) : Prop :=
  n ^ C < 2 ^ k

/-- Once the scale witness and solver capture are supplied, the tower load
strictly exceeds the polynomial budget. -/
theorem polynomial_budget_broken {load : Nat → Nat} {n k C : Nat}
    (capture : SolverCaptureDoubling load)
    (scale : SuperpolyScaleWitness n k C) :
    n ^ C < load k :=
  lt_of_lt_of_le scale (pow_two_le_load capture k)

/-- Canonical proposed succinct level `(log₂ n)^2`. -/
def logSquaredLevel (n : Nat) : Nat := (Nat.log 2 n) ^ 2

/-- The log-squared specialization.  The only arithmetic premise is displayed
verbatim; no asymptotic claim is smuggled into the solver-capture field. -/
theorem logSquared_budget_broken {load : Nat → Nat} {n C : Nat}
    (capture : SolverCaptureDoubling load)
    (scale : n ^ C < 2 ^ logSquaredLevel n) :
    n ^ C < load (logSquaredLevel n) :=
  polynomial_budget_broken capture scale

/-- A polynomial upper bound cannot coexist with a captured tower at any
explicit scale witness. -/
theorem no_poly_bound_at_witness {load : Nat → Nat} {n k C : Nat}
    (capture : SolverCaptureDoubling load)
    (scale : SuperpolyScaleWitness n k C) :
    ¬ load k ≤ n ^ C := by
  intro upper
  exact (not_lt_of_ge upper) (polynomial_budget_broken capture scale)

end PallLean.Paper93.DeepMath.PathB.GodelTowerSuperpolyScale

#print axioms PallLean.Paper93.DeepMath.PathB.GodelTowerSuperpolyScale.pow_two_le_load
#print axioms PallLean.Paper93.DeepMath.PathB.GodelTowerSuperpolyScale.polynomial_budget_broken
#print axioms PallLean.Paper93.DeepMath.PathB.GodelTowerSuperpolyScale.logSquared_budget_broken
#print axioms PallLean.Paper93.DeepMath.PathB.GodelTowerSuperpolyScale.no_poly_bound_at_witness
