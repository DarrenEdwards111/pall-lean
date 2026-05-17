import PallLean.Paper93.DeepMath.PathC.PiPlusSPDPTransportCriterion
import PallLean.SymmetricPower

/-!
# Local Pi+ / mlProj obstruction

The generator-transport target from `PiPlusSPDPTransportCriterion` is not a
routine consequence of algebra-equivalence alone.  This file records the local
reason in the kernel: the Hadamard `Pi+` sends a multilinear product in one
2-variable block to a difference of squares.  The ambient multilinear projection
then kills that quadratic leakage.

This does **not** refute Route C; it identifies the exact seam.  A successful
transport proof must account for the projection/Boolean quotient behavior, or
use a projected/quotiented Pi+ action, rather than treating the raw algebra
homomorphism as if it preserved multilinearity generator-by-generator.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open MultilinearSPDP
open PallLean.Paper93.NFrame

/-- Local quadratic leakage: the concrete two-variable Hadamard sends the
multilinear block product `X₀X₁` to `X₀² - X₁²`. -/
theorem piPlusHadamard2Gauge_mul_pair_leakage :
    piPlusHadamard2Gauge ((X 0) * (X 1) : MvPolynomial (Fin 2) ℚ) =
      (X 0 ^ 2 - X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) := by
  change rationalMatrixSubstAlgHom piPlusHadamard2Matrix ((X 0) * (X 1)) = _
  rw [map_mul]
  change piPlusHadamard2Gauge (X 0) * piPlusHadamard2Gauge (X 1) = _
  rw [piPlusHadamard2Gauge_X_zero, piPlusHadamard2Gauge_X_one]
  ring

/-- The multilinear projection kills the local quadratic leakage. -/
theorem mlProj_piPlusHadamard2Gauge_mul_pair_leakage :
    mlProj (piPlusHadamard2Gauge
      ((X 0) * (X 1) : MvPolynomial (Fin 2) ℚ)) = 0 := by
  rw [piPlusHadamard2Gauge_mul_pair_leakage]
  have hsub : (X 0 ^ 2 - X 1 ^ 2 : MvPolynomial (Fin 2) ℚ) =
      X 0 * X 0 + -(X 1 * X 1) := by
    ring
  rw [hsub, mlProj_add]
  have hneg : mlProj (-(X 1 * X 1 : MvPolynomial (Fin 2) ℚ)) =
      -mlProj (X 1 * X 1 : MvPolynomial (Fin 2) ℚ) := by
    have : (-(X 1 * X 1 : MvPolynomial (Fin 2) ℚ)) =
        (-1 : ℚ) • (X 1 * X 1 : MvPolynomial (Fin 2) ℚ) := by
      simp
    rw [this, mlProj_smul]
    simp
  rw [hneg, SymmetricPower.mlProj_X_sq_zero, SymmetricPower.mlProj_X_sq_zero]
  simp

/-! ## Axiom audit anchors -/

#print axioms piPlusHadamard2Gauge_mul_pair_leakage
#print axioms mlProj_piPlusHadamard2Gauge_mul_pair_leakage

end PallLean.Paper93.DeepMath.PathC
