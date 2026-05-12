import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# Structural lemmas about principal-TNN matrices

This file proves three structural lemmas about principal-TNN matrices:

* `principalTNN_empty`: The principal-TNN condition at the empty index set is
  always satisfied because the determinant of a `0 × 0` matrix is `1`.
* `principalTNN_diagonal_nonneg`: Principal-TNN at the singleton `{i}`
  forces the diagonal entry `A i i` to be non-negative.
* `principalTNN_det_nonneg`: Principal-TNN at the full universe forces
  the full determinant `A.det` to be non-negative.

These are basic invariants of the principal-TNN definition; they are stated in
terms of a *local* copy of the predicate so this file remains self-contained
and does not depend on `TNNMatrixDef.lean` building.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- `IsPrincipalTNN A` defined locally (in case the dependency file isn't built). -/
def IsPrincipalTNN_local {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ (J : Finset (Fin n)),
    0 ≤ (A.submatrix (fun i : J => (i.val : Fin n)) (fun j : J => (j.val : Fin n))).det

/-- Principal-TNN at the empty subset is automatic (det of 0×0 matrix is 1). -/
theorem principalTNN_empty {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ (A.submatrix (fun i : (∅ : Finset (Fin n)) => i.val)
                     (fun j : (∅ : Finset (Fin n)) => j.val)).det := by
  rw [Matrix.det_isEmpty]
  norm_num

/-- For a principal-TNN matrix, every diagonal entry is non-negative. -/
theorem principalTNN_diagonal_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsPrincipalTNN_local A) (i : Fin n) :
    0 ≤ A i i := by
  have h := hA {i}
  -- Principal submatrix at {i} is the 1×1 matrix [[A i i]]
  -- Its det is A i i
  have hUnique : Unique ({i} : Finset (Fin n)) := by
    refine ⟨⟨⟨i, Finset.mem_singleton.mpr rfl⟩⟩, ?_⟩
    rintro ⟨j, hj⟩
    have : j = i := Finset.mem_singleton.mp hj
    subst this
    rfl
  rw [Matrix.det_unique] at h
  -- After `det_unique`, `h : 0 ≤ A.submatrix (·.val) (·.val) default default`
  -- which unfolds to `0 ≤ A (default.val) (default.val)`. The unique element
  -- of `({i} : Finset (Fin n))` is `⟨i, _⟩`, hence `default.val = i`.
  simp only [Matrix.submatrix_apply] at h
  -- `default` in the singleton subtype is `⟨i, mem_singleton.mpr rfl⟩`,
  -- whose `.val` is `i` by uniqueness.
  have hdefault : (default : ({i} : Finset (Fin n))).val = i := by
    have := hUnique.uniq ⟨i, Finset.mem_singleton.mpr rfl⟩
    -- `default = ⟨i, _⟩`, so `default.val = i`.
    rw [← this]
  rw [hdefault] at h
  exact h

/-- For a principal-TNN matrix, the determinant is non-negative. -/
theorem principalTNN_det_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsPrincipalTNN_local A) :
    0 ≤ A.det := by
  have h := hA Finset.univ
  -- Principal submatrix at univ is A reindexed by the canonical equiv
  let e : (Finset.univ : Finset (Fin n)) ≃ Fin n :=
    Equiv.subtypeUnivEquiv (fun i : Fin n => Finset.mem_univ i)
  have hsub :
      A.submatrix (fun i : (Finset.univ : Finset (Fin n)) => i.val)
                  (fun j : (Finset.univ : Finset (Fin n)) => j.val)
        = A.submatrix e e := rfl
  rw [hsub] at h
  rw [Matrix.det_submatrix_equiv_self] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.Positroid
