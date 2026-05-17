import PallLean.Paper93.DeepMath.PathC.PiPlusAdmissibility
import PallLean.Paper93.NFrame.LinearSubstitutionGauge

/-!
# Concrete local Pi+ Hadamard polynomial gauge

This file lands the first *actual* concrete admissibility facts for the Route C
`Pi+` programme.  The SAT-scale `PiPlusSATTransform` still needs the full
Cook--Levin block-coordinate lift, but the local algebraic core is now real:
the radius-one Hadamard/Fourier substitution on two polynomial variables fixes
constants and sends the two variables to their sum/difference.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open PallLean.Paper93.NFrame

attribute [local instance] Classical.dec

/-! ## Two-variable Hadamard matrix over `ℚ` -/

/-- The unnormalised two-variable Hadamard/Fourier matrix used by local `Pi+`:
`X₀ ↦ X₀ + X₁`, `X₁ ↦ X₀ - X₁`. -/
noncomputable def piPlusHadamard2Matrix : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 1; 1, -1]

/-- The induced two-variable polynomial substitution gauge. -/
noncomputable def piPlusHadamard2Gauge :
    MvPolynomial (Fin 2) ℚ →ₗ[ℚ] MvPolynomial (Fin 2) ℚ :=
  rationalMatrixSubstGauge piPlusHadamard2Matrix

/-- Matrix entries of the local Hadamard block. -/
@[simp] theorem piPlusHadamard2Matrix_zero_zero :
    piPlusHadamard2Matrix (0 : Fin 2) (0 : Fin 2) = 1 := by
  norm_num [piPlusHadamard2Matrix]

@[simp] theorem piPlusHadamard2Matrix_zero_one :
    piPlusHadamard2Matrix (0 : Fin 2) (1 : Fin 2) = 1 := by
  norm_num [piPlusHadamard2Matrix]

@[simp] theorem piPlusHadamard2Matrix_one_zero :
    piPlusHadamard2Matrix (1 : Fin 2) (0 : Fin 2) = 1 := by
  norm_num [piPlusHadamard2Matrix]

@[simp] theorem piPlusHadamard2Matrix_one_one :
    piPlusHadamard2Matrix (1 : Fin 2) (1 : Fin 2) = -1 := by
  norm_num [piPlusHadamard2Matrix]

/-- Any rational matrix-induced polynomial substitution fixes constants.  This
is the concrete unit-preservation fact needed by `PiPlusUnitPreserving`. -/
@[simp] theorem rationalMatrixSubstGauge_one_poly {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℚ) :
    rationalMatrixSubstGauge A (1 : MvPolynomial (Fin N) ℚ) = 1 := by
  simpa using rationalMatrixSubstGauge_C (N := N) A (1 : ℚ)

/-- The local `Pi+` Hadamard gauge is unit-preserving. -/
theorem piPlusHadamard2Gauge_unitPreserving :
    piPlusHadamard2Gauge (1 : MvPolynomial (Fin 2) ℚ) = 1 := by
  simp [piPlusHadamard2Gauge]

/-- First variable maps to the sum coordinate. -/
theorem piPlusHadamard2Gauge_X_zero :
    piPlusHadamard2Gauge (X (0 : Fin 2)) =
      (X (0 : Fin 2) + X (1 : Fin 2) : MvPolynomial (Fin 2) ℚ) := by
  classical
  unfold piPlusHadamard2Gauge piPlusHadamard2Matrix
  rw [rationalMatrixSubstGauge_X]
  unfold rationalMatrixLinearForm
  simp [Fin.sum_univ_two]

/-- Second variable maps to the difference coordinate. -/
theorem piPlusHadamard2Gauge_X_one :
    piPlusHadamard2Gauge (X (1 : Fin 2)) =
      (X (0 : Fin 2) - X (1 : Fin 2) : MvPolynomial (Fin 2) ℚ) := by
  classical
  unfold piPlusHadamard2Gauge piPlusHadamard2Matrix
  rw [rationalMatrixSubstGauge_X]
  unfold rationalMatrixLinearForm
  simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- Concrete local admissibility core: the two-variable Hadamard polynomial
substitution fixes units and has the expected generator action. -/
def PiPlusHadamard2LocalAdmissibilityCore : Prop :=
  piPlusHadamard2Gauge (1 : MvPolynomial (Fin 2) ℚ) = 1 ∧
    piPlusHadamard2Gauge (X (0 : Fin 2)) =
      (X (0 : Fin 2) + X (1 : Fin 2) : MvPolynomial (Fin 2) ℚ) ∧
    piPlusHadamard2Gauge (X (1 : Fin 2)) =
      (X (0 : Fin 2) - X (1 : Fin 2) : MvPolynomial (Fin 2) ℚ)

/-- The local admissibility core is now kernel-checked. -/
theorem piPlusHadamard2_localAdmissibilityCore :
    PiPlusHadamard2LocalAdmissibilityCore :=
  ⟨piPlusHadamard2Gauge_unitPreserving,
    piPlusHadamard2Gauge_X_zero,
    piPlusHadamard2Gauge_X_one⟩

/-! ## Axiom audit anchors -/

#print axioms rationalMatrixSubstGauge_one_poly
#print axioms piPlusHadamard2Gauge_unitPreserving
#print axioms piPlusHadamard2Gauge_X_zero
#print axioms piPlusHadamard2Gauge_X_one
#print axioms piPlusHadamard2_localAdmissibilityCore

end PallLean.Paper93.DeepMath.PathC
