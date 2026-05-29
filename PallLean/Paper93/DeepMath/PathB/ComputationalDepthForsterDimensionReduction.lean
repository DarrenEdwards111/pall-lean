import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthForsterScaffold

/-!
# Forster dimension reduction: restrict a realization to its row span

The corrected Forster kernel in `ComputationalDepthForsterScaffold` applies to
**spanning** unit realizations.  This file proves the standard finite-dimensional
cleanup step: any unit sign-realization can be restricted to the span of its row
vectors, without changing signs, and the new row vectors span by construction.

The construction is concrete:

* let `U = span {u_i}`;
* project each column vector `w_j` to `U`;
* use an orthonormal basis of `U` to identify `U` with `ℝ^k`;
* normalize the projected columns.

This is the tractable companion to the analytic isotropic-position lemma.  It
does **not** prove the isotropic-position existence theorem; it removes the
non-spanning slack around it.
-/

namespace PallLean.Paper93.DeepMath.PathB.Forster

open scoped InnerProductSpace BigOperators Matrix Matrix.Norms.L2Operator
open RealInnerProductSpace

noncomputable section

variable {m n : Nat}

/-- The row span of a unit sign-realization. -/
def rowSpan {M : Fin m -> Fin n -> Bool} {d : Nat}
    (R : UnitRealization M d) : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℝ (Set.range R.u)

theorem row_mem_rowSpan {M : Fin m -> Fin n -> Bool} {d : Nat}
    (R : UnitRealization M d) (i : Fin m) :
    R.u i ∈ rowSpan R :=
  Submodule.subset_span ⟨i, rfl⟩

/-- Inside the row span, the original row vectors span the whole subspace. -/
theorem subtype_rows_span_rowSpan {M : Fin m -> Fin n -> Bool} {d : Nat}
    (R : UnitRealization M d) :
    Submodule.span ℝ
        (Set.range fun i : Fin m => (⟨R.u i, row_mem_rowSpan R i⟩ : rowSpan R)) = ⊤ := by
  rw [Submodule.span_range_subtype_eq_top_iff (p := rowSpan R)
    (hs := fun i => row_mem_rowSpan R i)]
  rfl

/-- The coordinate rows obtained from an orthonormal basis of the row span span
the target Euclidean space. -/
theorem coord_rows_span_top {M : Fin m -> Fin n -> Bool} {d : Nat}
    (R : UnitRealization M d) :
    Submodule.span ℝ
        (Set.range fun i : Fin m =>
          (stdOrthonormalBasis ℝ (rowSpan R)).repr
            (⟨R.u i, row_mem_rowSpan R i⟩ : rowSpan R)) = ⊤ := by
  classical
  let b := stdOrthonormalBasis ℝ (rowSpan R)
  have hspan := subtype_rows_span_rowSpan R
  calc
    Submodule.span ℝ
        (Set.range fun i : Fin m =>
          (stdOrthonormalBasis ℝ (rowSpan R)).repr
            (⟨R.u i, row_mem_rowSpan R i⟩ : rowSpan R))
        =
        Submodule.span ℝ
          ((stdOrthonormalBasis ℝ (rowSpan R)).repr ''
            Set.range (fun i : Fin m =>
              (⟨R.u i, row_mem_rowSpan R i⟩ : rowSpan R))) := by
          congr 1
          ext x
          constructor
          · rintro ⟨i, rfl⟩
            exact ⟨⟨R.u i, row_mem_rowSpan R i⟩, ⟨i, rfl⟩, rfl⟩
          · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
            exact ⟨i, rfl⟩
    _ =
        Submodule.map ((stdOrthonormalBasis ℝ (rowSpan R)).repr : rowSpan R →ₗ[ℝ]
          EuclideanSpace ℝ (Fin (Module.finrank ℝ (rowSpan R))))
          (Submodule.span ℝ
            (Set.range fun i : Fin m =>
              (⟨R.u i, row_mem_rowSpan R i⟩ : rowSpan R))) := by
          simpa using
            (Submodule.span_image
              (((stdOrthonormalBasis ℝ (rowSpan R)).repr : rowSpan R ≃ₗᵢ[ℝ]
                EuclideanSpace ℝ (Fin (Module.finrank ℝ (rowSpan R)))) :
                  rowSpan R →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (rowSpan R))))
              (s := Set.range fun i : Fin m =>
                (⟨R.u i, row_mem_rowSpan R i⟩ : rowSpan R)))
    _ = ⊤ := by
          rw [hspan, Submodule.map_top]
          exact LinearEquiv.range _

/-- Projection of a column vector to the row span. -/
def rowSpanProjectedColumn {M : Fin m -> Fin n -> Bool} {d : Nat}
    (R : UnitRealization M d) (j : Fin n) : rowSpan R :=
  (rowSpan R).orthogonalProjection (R.w j)

/-- The projected column is nonzero as soon as there is at least one row: every
original column has nonzero inner product with every row, and projection preserves
inner products against row-span vectors. -/
theorem rowSpanProjectedColumn_ne_zero {M : Fin m -> Fin n -> Bool} {d : Nat}
    (R : UnitRealization M d) (hm : 0 < m) (j : Fin n) :
    rowSpanProjectedColumn R j ≠ 0 := by
  classical
  let i : Fin m := ⟨0, hm⟩
  intro hzero
  have hinner_pres :
      (⟪(⟨R.u i, row_mem_rowSpan R i⟩ : rowSpan R), rowSpanProjectedColumn R j⟫ : ℝ)
        = ⟪R.u i, R.w j⟫ := by
    simp [rowSpanProjectedColumn]
  have hinner_zero : (⟪R.u i, R.w j⟫ : ℝ) = 0 := by
    rw [← hinner_pres, hzero, inner_zero_right]
  have hpos := R.sign_ok i j
  rw [hinner_zero, mul_zero] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

/-- The row-span restriction of a unit realization.  The new dimension is the
dimension of the row span. -/
def rowSpanRestriction {M : Fin m -> Fin n -> Bool} {d : Nat}
    (R : UnitRealization M d) (hm : 0 < m) :
    UnitRealization M (Module.finrank ℝ (rowSpan R)) where
  u i :=
    (stdOrthonormalBasis ℝ (rowSpan R)).repr
      (⟨R.u i, row_mem_rowSpan R i⟩ : rowSpan R)
  w j :=
    (‖(stdOrthonormalBasis ℝ (rowSpan R)).repr (rowSpanProjectedColumn R j)‖)⁻¹ •
      (stdOrthonormalBasis ℝ (rowSpan R)).repr (rowSpanProjectedColumn R j)
  u_unit := by
    intro i
    rw [LinearIsometryEquiv.norm_map]
    exact R.u_unit i
  w_unit := by
    intro j
    have hpos :
        0 < ‖(stdOrthonormalBasis ℝ (rowSpan R)).repr (rowSpanProjectedColumn R j)‖ := by
      rw [norm_pos_iff]
      intro h
      exact rowSpanProjectedColumn_ne_zero R hm j
        ((stdOrthonormalBasis ℝ (rowSpan R)).repr.injective
          (by simpa using h))
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos,
      inv_mul_cancel₀ (ne_of_gt hpos)]
  sign_ok := by
    intro i j
    let b := stdOrthonormalBasis ℝ (rowSpan R)
    have hpos :
        0 < ‖b.repr (rowSpanProjectedColumn R j)‖ := by
      rw [norm_pos_iff]
      intro h
      exact rowSpanProjectedColumn_ne_zero R hm j
        (b.repr.injective (by simpa using h))
    have hinner :
        (⟪b.repr (⟨R.u i, row_mem_rowSpan R i⟩ : rowSpan R),
            b.repr (rowSpanProjectedColumn R j)⟫ : ℝ) =
          ⟪R.u i, R.w j⟫ := by
      calc
        (⟪b.repr (⟨R.u i, row_mem_rowSpan R i⟩ : rowSpan R),
            b.repr (rowSpanProjectedColumn R j)⟫ : ℝ)
            = ⟪(⟨R.u i, row_mem_rowSpan R i⟩ : rowSpan R),
                rowSpanProjectedColumn R j⟫ := by
              rw [LinearIsometryEquiv.inner_map_map]
        _ = ⟪R.u i, R.w j⟫ := by
              simp [rowSpanProjectedColumn]
    have hscale :
        0 < (‖b.repr (rowSpanProjectedColumn R j)‖)⁻¹ :=
      inv_pos.mpr hpos
    dsimp [b]
    rw [real_inner_smul_right, hinner]
    have hsign := R.sign_ok i j
    nlinarith [hscale, hsign]

theorem rowSpanRestriction_spans {M : Fin m -> Fin n -> Bool} {d : Nat}
    (R : UnitRealization M d) (hm : 0 < m) :
    Spans (rowSpanRestriction R hm) := by
  simpa [Spans, rowSpanRestriction] using coord_rows_span_top R

theorem rowSpan_finrank_pos {M : Fin m -> Fin n -> Bool} {d : Nat}
    (R : UnitRealization M d) (hm : 0 < m) :
    0 < Module.finrank ℝ (rowSpan R) := by
  classical
  let i : Fin m := ⟨0, hm⟩
  rw [Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨(⟨R.u i, row_mem_rowSpan R i⟩ : rowSpan R), ?_⟩
  intro h
  have hu0 : R.u i = 0 := Subtype.ext_iff.mp h
  have hunit := R.u_unit i
  rw [hu0, norm_zero] at hunit
  exact one_ne_zero hunit.symm

/-- Any unit realization admits a lower-dimensional spanning unit realization:
restrict to the row span and coordinate it by an orthonormal basis. -/
theorem exists_spanning_restriction {M : Fin m -> Fin n -> Bool} {d : Nat}
    (R : UnitRealization M d) (hm : 0 < m) :
    ∃ k : Nat, 0 < k ∧ k ≤ d ∧ ∃ Rred : UnitRealization M k, Spans Rred := by
  have hle : Module.finrank ℝ (rowSpan R) ≤ d := by
    have hle' :
        Module.finrank ℝ (rowSpan R) ≤
          Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) :=
      Submodule.finrank_le _
    simpa using hle'
  refine ⟨Module.finrank ℝ (rowSpan R), rowSpan_finrank_pos R hm, hle, ?_⟩
  exact ⟨rowSpanRestriction R hm, rowSpanRestriction_spans R hm⟩

/-- Forster, modulo the corrected isotropic kernel, for an arbitrary
non-minimal unit realization.  The realization is first restricted to its row
span; Forster is applied there; then `k ≤ d` transfers the bound back to the
original ambient dimension. -/
theorem forster_of_kernel_any_realization (M : Fin m -> Fin n -> Bool)
    (hker : IsotropicKernel M) {d : Nat} (R : UnitRealization M d)
    (hm : 0 < m) (hmn : 0 < (m : ℝ) * n) (hμ : 0 < ‖sgnMat M‖) :
    Real.sqrt ((m : ℝ) * n) / ‖sgnMat M‖ ≤ (d : ℝ) := by
  obtain ⟨k, hkpos, hk_le, Rred, hspan⟩ := exists_spanning_restriction R hm
  have hbound :
      Real.sqrt ((m : ℝ) * n) / ‖sgnMat M‖ ≤ (k : ℝ) :=
    forster_of_kernel M hker Rred hspan hkpos hmn hμ
  exact hbound.trans (by exact_mod_cast hk_le)

#print axioms coord_rows_span_top
#print axioms rowSpanRestriction
#print axioms exists_spanning_restriction
#print axioms forster_of_kernel_any_realization

end

end PallLean.Paper93.DeepMath.PathB.Forster
