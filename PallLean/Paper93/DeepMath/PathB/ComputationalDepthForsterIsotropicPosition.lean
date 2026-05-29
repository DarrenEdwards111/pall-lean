import PallLean.Paper93.DeepMath.PathB.ComputationalDepthForsterDimensionReduction

/-!
# Forster isotropic-position lemmas

This file starts the analytic isotropic-position gate directly.  It does **not**
fake the full Forster/Barthe existence theorem.  Instead it proves two exact
pieces that are useful guardrails for the remaining long-haul theorem:

* if the rows are already tight, the identity transform is a valid transform;
* in ambient dimension `1`, every unit realization is already tight, hence the
  transform exists unconditionally.

The general `d ≥ 2` spanning isotropic-position theorem remains the compactness /
variational minimization project.
-/

namespace PallLean.Paper93.DeepMath.PathB.Forster

open scoped InnerProductSpace BigOperators Matrix Matrix.Norms.L2Operator
open RealInnerProductSpace

noncomputable section

variable {m n : Nat}

/-- The transform-existence target consumed by `isotropicKernel_of_transform`. -/
def IsotropicTransformExists {M : Fin m -> Fin n -> Bool} {d : Nat}
    (R : UnitRealization M d) : Prop :=
  ∃ T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d),
    ∀ y, ∑ i, ⟪(‖T (R.u i)‖)⁻¹ • T (R.u i), y⟫ ^ 2 =
      ((m : ℝ) / d) * ‖y‖ ^ 2

/-- If the row vectors are already in tight-frame position, the identity map is
the required isotropic transform. -/
theorem isotropicTransform_of_tightFrame {M : Fin m -> Fin n -> Bool} {d : Nat}
    (R : UnitRealization M d) (hframe : IsTightFrame R) :
    IsotropicTransformExists R := by
  refine ⟨LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin d)), ?_⟩
  intro y
  convert hframe y using 2 with i
  rw [LinearEquiv.refl_apply, R.u_unit i, inv_one, one_smul]

/-- In one dimension, each unit row has inner product square exactly `‖y‖²` with
every vector `y`. -/
theorem one_dim_inner_sq_eq_norm_sq {M : Fin m -> Fin n -> Bool}
    (R : UnitRealization M 1) (i : Fin m) (y : EuclideanSpace ℝ (Fin 1)) :
    ⟪R.u i, y⟫ ^ 2 = ‖y‖ ^ 2 := by
  have hu_sq : (R.u i 0) ^ 2 = 1 := by
    have hunit_sq : ‖R.u i‖ ^ 2 = (1 : ℝ) := by rw [R.u_unit i, one_pow]
    rw [eucl_normSq_eq_sum] at hunit_sq
    simpa using hunit_sq
  rw [eucl_inner_eq_sum, eucl_normSq_eq_sum]
  simp only [Fin.sum_univ_one]
  nlinarith [hu_sq]

/-- Every one-dimensional unit realization is automatically a tight frame. -/
theorem tightFrame_dim_one {M : Fin m -> Fin n -> Bool}
    (R : UnitRealization M 1) : IsTightFrame R := by
  intro y
  calc
    ∑ i, ⟪R.u i, y⟫ ^ 2
        = ∑ _i : Fin m, ‖y‖ ^ 2 := by
          exact Finset.sum_congr rfl (fun i _ => one_dim_inner_sq_eq_norm_sq R i y)
    _ = (m : ℝ) * ‖y‖ ^ 2 := by simp
    _ = ((m : ℝ) / (1 : Nat)) * ‖y‖ ^ 2 := by norm_num

/-- The isotropic-position transform exists unconditionally in dimension `1`. -/
theorem isotropicTransform_dim_one {M : Fin m -> Fin n -> Bool}
    (R : UnitRealization M 1) : IsotropicTransformExists R :=
  isotropicTransform_of_tightFrame R (tightFrame_dim_one R)

#print axioms isotropicTransform_of_tightFrame
#print axioms tightFrame_dim_one
#print axioms isotropicTransform_dim_one

end

end PallLean.Paper93.DeepMath.PathB.Forster
