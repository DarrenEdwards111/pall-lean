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

One important guardrail is now explicit too: the naive equal-weight transform
target is false for arbitrary spanning rows.  Duplicate rows cannot be separated
by an invertible map, and three unit rows in dimension two with a duplicate row
cannot become a tight frame after normalization.  The full Forster/Barthe kernel
therefore needs the correct balance hypothesis (or a weighted/minimal-position
formulation), not mere spanning.
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

/-- The naive general transform target is false: three rows in dimension two
with a duplicate row cannot be normalized by any invertible map into an
equal-weight tight frame.  Indeed the two duplicate normalized rows contribute
`2` in their common direction, while tightness would require total mass `3 / 2`
in every unit direction. -/
theorem not_isotropicTransformExists_duplicate_three_dim_two
    {M : Fin 3 -> Fin n -> Bool} (R : UnitRealization M 2)
    (hdup : R.u 0 = R.u 1) :
    ¬ IsotropicTransformExists R := by
  rintro ⟨T, hT⟩
  have hu0_ne : R.u 0 ≠ 0 := by
    intro h
    have hunit := R.u_unit 0
    rw [h, norm_zero] at hunit
    exact one_ne_zero hunit.symm
  have hTpos : 0 < ‖T (R.u 0)‖ := by
    rw [norm_pos_iff]
    intro hzero
    exact hu0_ne (T.injective (by simpa using hzero))
  let v : EuclideanSpace ℝ (Fin 2) := (‖T (R.u 0)‖)⁻¹ • T (R.u 0)
  have hvnorm : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hTpos,
      inv_mul_cancel₀ (ne_of_gt hTpos)]
  let z : Fin 3 -> EuclideanSpace ℝ (Fin 2) :=
    fun i => (‖T (R.u i)‖)⁻¹ • T (R.u i)
  have hz0 : z 0 = v := rfl
  have hz1 : z 1 = v := by
    dsimp [z, v]
    rw [← hdup]
  have hvinner : (⟪v, v⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hvnorm]
    norm_num
  have h0 : (⟪z 0, v⟫ : ℝ) ^ 2 = 1 := by
    rw [hz0, hvinner]
    norm_num
  have h1 : (⟪z 1, v⟫ : ℝ) ^ 2 = 1 := by
    rw [hz1, hvinner]
    norm_num
  have h2 : 0 ≤ (⟪z 2, v⟫ : ℝ) ^ 2 := sq_nonneg _
  have hsum_ge : (2 : ℝ) ≤ ∑ i : Fin 3, (⟪z i, v⟫ : ℝ) ^ 2 := by
    rw [Fin.sum_univ_three]
    nlinarith
  have htight := hT v
  change (∑ i : Fin 3, (⟪z i, v⟫ : ℝ) ^ 2)
      = ((3 : ℝ) / (2 : Nat)) * ‖v‖ ^ 2 at htight
  have hsum_eq : (∑ i : Fin 3, (⟪z i, v⟫ : ℝ) ^ 2) = (3 : ℝ) / 2 := by
    rw [htight, hvnorm]
    norm_num
  have hbad : (2 : ℝ) ≤ (3 : ℝ) / 2 := by
    linarith
  norm_num at hbad

/-- Same obstruction, stated with the currently tempting spanning hypothesis:
spanning alone does not repair duplicate-row overload.  The `Spans` assumption is
deliberately unused; the point is that it is too weak for the equal-weight
transform target. -/
theorem not_isotropicTransformExists_of_spans_duplicate_three_dim_two
    {M : Fin 3 -> Fin n -> Bool} (R : UnitRealization M 2)
    (_hspan : Spans R) (hdup : R.u 0 = R.u 1) :
    ¬ IsotropicTransformExists R :=
  not_isotropicTransformExists_duplicate_three_dim_two R hdup

#print axioms isotropicTransform_of_tightFrame
#print axioms tightFrame_dim_one
#print axioms isotropicTransform_dim_one
#print axioms not_isotropicTransformExists_duplicate_three_dim_two
#print axioms not_isotropicTransformExists_of_spans_duplicate_three_dim_two

end

end PallLean.Paper93.DeepMath.PathB.Forster
