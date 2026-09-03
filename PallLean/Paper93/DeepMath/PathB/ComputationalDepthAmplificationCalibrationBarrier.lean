import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMemoryRobustCrossingCost
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPSeparatingInvariant

/-!
# Amplification calibration barrier

The bounded-pass reuse-cost lower bound is linear.  A tempting next step is to
apply a generic numerical amplifier (exponentiation, repeated powering, and so
on) to make that floor super-polynomial.  This file proves why that cannot be
the missing argument while retaining the universal P-side calibration.

An amplifier is polynomially calibrated when it maps every polynomially
bounded resource profile to another polynomially bounded profile.  The linear
floor `2n` is polynomially bounded.  Therefore every calibrated amplifier maps
that floor to a polynomially bounded function.  Conversely, any amplifier
that makes the floor non-polynomial necessarily fails calibration on this
explicit polynomial input.

Thus no representation-independent numerical rescaling upgrades the proved
linear bound into the missing SAT lower bound.  A successful amplification
must use new family/algorithm structure, not merely post-process the resource
value.  This is a no-go theorem, not `P != NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.AmplificationCalibrationBarrier

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant



/-- The explicit linear reuse-cost floor from the one-block theorem. -/
def linearFloor (n : ℕ) : ℕ := 2 * n


/-- A generic numerical amplifier preserves the P-side requirement when it
maps every polynomially bounded profile to a polynomially bounded profile. -/
def PolynomiallyCalibrated (A : ℕ → ℕ → ℕ) : Prop :=
  ∀ cost : ℕ → ℕ, PolyBounded cost →
    PolyBounded (fun n => A n (cost n))

/-- The proved restricted lower-bound floor is polynomially bounded. -/
theorem linearFloor_polyBounded : PolyBounded linearFloor := by
  refine ⟨2, 1, fun n => ?_⟩
  simp [linearFloor]

/-- **Calibration barrier.** A P-calibrated numerical amplifier cannot turn
the linear floor into a non-polynomial profile. -/
theorem calibrated_cannot_make_linearFloor_superpoly
    (A : ℕ → ℕ → ℕ) (hA : PolynomiallyCalibrated A) :
    PolyBounded (fun n => A n (linearFloor n)) :=
  hA linearFloor linearFloor_polyBounded

/-- Contrapositive form: if an amplifier makes the linear floor
non-polynomial, then it fails the universal polynomial calibration. -/
theorem superpoly_floor_breaks_calibration
    (A : ℕ → ℕ → ℕ)
    (hSuper : ¬ PolyBounded (fun n => A n (linearFloor n))) :
    ¬ PolynomiallyCalibrated A := by
  intro hA
  exact hSuper (calibrated_cannot_make_linearFloor_superpoly A hA)

/-- The obstruction already appears on the concrete linear profile; a failed
calibration has an explicit polynomially bounded witness. -/
theorem superpoly_floor_has_polynomial_counterexample
    (A : ℕ → ℕ → ℕ)
    (hSuper : ¬ PolyBounded (fun n => A n (linearFloor n))) :
    ∃ cost, PolyBounded cost ∧
      ¬ PolyBounded (fun n => A n (cost n)) :=
  ⟨linearFloor, linearFloor_polyBounded, hSuper⟩

end PallLean.Paper93.DeepMath.PathB.AmplificationCalibrationBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.AmplificationCalibrationBarrier.linearFloor_polyBounded
#print axioms PallLean.Paper93.DeepMath.PathB.AmplificationCalibrationBarrier.calibrated_cannot_make_linearFloor_superpoly
#print axioms PallLean.Paper93.DeepMath.PathB.AmplificationCalibrationBarrier.superpoly_floor_breaks_calibration
#print axioms PallLean.Paper93.DeepMath.PathB.AmplificationCalibrationBarrier.superpoly_floor_has_polynomial_counterexample
