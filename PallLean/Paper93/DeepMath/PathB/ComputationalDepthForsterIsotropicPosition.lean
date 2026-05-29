import Mathlib.LinearAlgebra.Dimension.OrzechProperty
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

/-- A corrected weighted/basis-subset isotropic target.  Instead of forcing every
row to carry equal mass, select a basis of rows and put total mass `m` on that
basis, with weight `m / d` per selected basis row.  Redundant rows are therefore
allowed to have zero weight, avoiding the duplicate-row obstruction below. -/
def SelectedBasisWeightedIsotropicTransformExists
    {M : Fin m -> Fin n -> Bool} {d : Nat} (R : UnitRealization M d)
    {κ : Type*} [Fintype κ] (select : κ -> Fin m) : Prop :=
  ∃ T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d),
    ∀ y, ∑ k : κ,
        ((m : ℝ) / d) *
          ⟪(‖T (R.u (select k))‖)⁻¹ • T (R.u (select k)), y⟫ ^ 2 =
      ((m : ℝ) / d) * ‖y‖ ^ 2

/-- Packaged corrected target: a finite, injectively selected basis subset of
rows carries the isotropic mass. -/
def BasisWeightedIsotropicTransformExists
    {M : Fin m -> Fin n -> Bool} {d : Nat} (R : UnitRealization M d) : Prop :=
  ∃ (κ : Type) (inst : Fintype κ) (select : κ -> Fin m),
    Function.Injective select ∧ Fintype.card κ = d ∧
      @SelectedBasisWeightedIsotropicTransformExists m n M d R κ inst select

/-- If the selected rows form a basis of the ambient space, the corrected
weighted target is provable without compactness: map that basis to an
orthonormal basis and put the isotropic mass on the selected basis rows. -/
theorem selectedBasisWeightedIsotropicTransform_of_selected_basis
    {M : Fin m -> Fin n -> Bool} {d : Nat} (R : UnitRealization M d)
    {κ : Type*} [Fintype κ] (select : κ -> Fin m)
    (hcard : Fintype.card κ = d)
    (hli : LinearIndependent ℝ (fun k => R.u (select k)))
    (hspan : Submodule.span ℝ (Set.range fun k => R.u (select k)) = ⊤) :
    SelectedBasisWeightedIsotropicTransformExists R select := by
  classical
  let b : Module.Basis κ ℝ (EuclideanSpace ℝ (Fin d)) :=
    Module.Basis.mk hli (by rw [hspan])
  let e : κ ≃ Fin d := Fintype.equivOfCardEq (by simpa using hcard)
  let stdON : OrthonormalBasis κ ℝ (EuclideanSpace ℝ (Fin d)) :=
    (EuclideanSpace.basisFun (Fin d) ℝ).reindex e.symm
  let std : Module.Basis κ ℝ (EuclideanSpace ℝ (Fin d)) := stdON.toBasis
  let T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    b.equiv std (Equiv.refl κ)
  refine ⟨T, ?_⟩
  intro y
  have hnormed :
      ∀ k : κ, (‖T (R.u (select k))‖)⁻¹ • T (R.u (select k)) = stdON k := by
    intro k
    have hmap : T (R.u (select k)) = stdON k := by
      have h := Module.Basis.equiv_apply b k std (Equiv.refl κ)
      simpa [T, b, std] using h
    rw [hmap, stdON.norm_eq_one k, inv_one, one_smul]
  calc
    ∑ k : κ,
        ((m : ℝ) / d) *
          ⟪(‖T (R.u (select k))‖)⁻¹ • T (R.u (select k)), y⟫ ^ 2
        = ∑ k : κ, ((m : ℝ) / d) * ⟪stdON k, y⟫ ^ 2 := by
          exact Finset.sum_congr rfl (fun k _ => by rw [hnormed k])
    _ = ((m : ℝ) / d) * ∑ k : κ, ⟪stdON k, y⟫ ^ 2 := by
          rw [Finset.mul_sum]
    _ = ((m : ℝ) / d) * ‖y‖ ^ 2 := by
          rw [stdON.sum_sq_inner_right y]

/-- Every spanning row realization has the corrected weighted/basis-subset
isotropic transform: choose a linearly independent subfamily of the rows with the
same span, map it to an orthonormal basis, and put zero weight on all redundant
rows.  This is the honest replacement for the false equal-weight spanning target. -/
theorem basisWeightedIsotropicTransform_of_spans
    {M : Fin m -> Fin n -> Bool} {d : Nat} (R : UnitRealization M d)
    (hspan : Spans R) :
    BasisWeightedIsotropicTransformExists R := by
  classical
  obtain ⟨κ, select, hselect_inj, hselect_span, hselect_li⟩ :=
    exists_linearIndependent' ℝ R.u
  letI : Fintype κ := Fintype.ofInjective select hselect_inj
  have hselected_span :
      Submodule.span ℝ (Set.range fun k : κ => R.u (select k)) = ⊤ := by
    have hspan' :
        Submodule.span ℝ (Set.range fun k : κ => R.u (select k))
          = Submodule.span ℝ (Set.range R.u) := by
      simpa [Function.comp_def] using hselect_span
    rw [hspan', hspan]
  have hselected_li :
      LinearIndependent ℝ (fun k : κ => R.u (select k)) := by
    simpa [Function.comp_def] using hselect_li
  have hcard : Fintype.card κ = d := by
    have hc :=
      (linearIndependent_iff_card_eq_finrank_span
        (R := ℝ) (M := EuclideanSpace ℝ (Fin d))
        (b := fun k : κ => R.u (select k))).mp hselected_li
    rw [Set.finrank, hselected_span, finrank_top, finrank_euclideanSpace] at hc
    simpa using hc
  refine ⟨κ, inferInstance, select, hselect_inj, hcard, ?_⟩
  exact selectedBasisWeightedIsotropicTransform_of_selected_basis
    R select hcard hselected_li hselected_span

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
#print axioms selectedBasisWeightedIsotropicTransform_of_selected_basis
#print axioms basisWeightedIsotropicTransform_of_spans
#print axioms not_isotropicTransformExists_duplicate_three_dim_two
#print axioms not_isotropicTransformExists_of_spans_duplicate_three_dim_two

end

end PallLean.Paper93.DeepMath.PathB.Forster
