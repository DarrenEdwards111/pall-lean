import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Real.Basic
import Mathlib.Order.WellFounded

/-!
# Total nonnegativity for real matrices

This file defines total nonnegativity for real square matrices: a matrix is
*totally nonneg* if every square minor (determinant of a square submatrix
indexed by strictly-monotone row/column selectors) is nonnegative.

We prove that the identity matrix is totally nonneg. The proof case-splits on
whether the row and column selectors agree:

* if `r = c`, the submatrix is itself the identity on `Fin k` via
  `Matrix.submatrix_one`, so its determinant is `1 ≥ 0`;
* if `r ≠ c`, then by `StrictMono.range_inj` their ranges differ as sets of
  `Fin n`. Since neither can be a proper subset of the other (they share the
  common source `Fin k`), either some `r i` is outside the column image or
  some `c j` is outside the row image; that row or column of the submatrix is
  uniformly zero, forcing the determinant to be `0 ≥ 0`.
-/

namespace PallLean.Paper93.DeepMath.Amplituhedron

open Matrix

/-- Square submatrix minor: determinant of the submatrix with rows `r` and
columns `c` of equal size `k`. -/
def minor {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    {k : ℕ} (r c : Fin k → Fin n) : ℝ :=
  (M.submatrix r c).det

/-- A matrix is totally nonneg if every square minor (over strictly-monotone
row/column index selectors) is nonnegative. -/
def TotallyNonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ {k : ℕ} (r c : Fin k → Fin n), StrictMono r → StrictMono c → 0 ≤ minor M r c

/-- If `r, c : Fin k → Fin n` are both strictly monotone and differ as
functions, then either some `r i` is outside the image of `c`, or some `c j`
is outside the image of `r`. -/
private lemma exists_row_or_col_out_of_range
    {n k : ℕ} {r c : Fin k → Fin n}
    (hr : StrictMono r) (hc : StrictMono c) (hrc : r ≠ c) :
    (∃ i : Fin k, ∀ j : Fin k, r i ≠ c j) ∨
      (∃ j : Fin k, ∀ i : Fin k, r i ≠ c j) := by
  -- Suppose both negations hold. Then `Set.range r ⊆ Set.range c` and
  -- `Set.range c ⊆ Set.range r`, hence `Set.range r = Set.range c`, and
  -- `StrictMono.range_inj` forces `r = c`, contradicting `hrc`.
  by_contra hneg
  push_neg at hneg
  obtain ⟨hRC, hCR⟩ := hneg
  have hrange : Set.range r = Set.range c := by
    apply Set.eq_of_subset_of_subset
    · rintro x ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hRC i
      exact ⟨j, hj.symm⟩
    · rintro x ⟨j, rfl⟩
      obtain ⟨i, hi⟩ := hCR j
      exact ⟨i, hi⟩
  exact hrc ((hr.range_inj hc).mp hrange)

/-- The identity matrix is totally nonneg: every square minor of the
`n × n` identity is either `0` or `1`, hence nonnegative. -/
theorem identity_totallyNonneg (n : ℕ) :
    TotallyNonneg (1 : Matrix (Fin n) (Fin n) ℝ) := by
  intro k r c hr hc
  unfold minor
  -- Case split on whether `r = c` as functions.
  by_cases hrc : r = c
  · -- The submatrix is the identity, determinant is `1 ≥ 0`.
    have hinj : Function.Injective r := hr.injective
    have hsub : (1 : Matrix (Fin n) (Fin n) ℝ).submatrix r c = 1 := by
      rw [hrc]; exact Matrix.submatrix_one c hc.injective
    rw [hsub, Matrix.det_one]
    exact zero_le_one
  · -- The submatrix has either a zero row or a zero column, so det = 0.
    rcases exists_row_or_col_out_of_range hr hc hrc with
      ⟨i, hi⟩ | ⟨j, hj⟩
    · -- Row `i` of the submatrix is zero: for every `j`, entry is
      -- `1 (r i) (c j) = 0` since `r i ≠ c j`.
      have hrow : ∀ j, ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix r c) i j = 0 := by
        intro j
        simp [Matrix.submatrix_apply, Matrix.one_apply_ne (hi j)]
      rw [Matrix.det_eq_zero_of_row_eq_zero i hrow]
    · -- Column `j` of the submatrix is zero. Pass through the transpose:
      -- `det M = det Mᵀ` and `Mᵀ` has row `j` equal to zero.
      have hcol : ∀ i,
          ((1 : Matrix (Fin n) (Fin n) ℝ).submatrix r c)ᵀ j i = 0 := by
        intro i
        simp [Matrix.transpose_apply, Matrix.submatrix_apply,
              Matrix.one_apply_ne (hj i)]
      rw [← Matrix.det_transpose,
          Matrix.det_eq_zero_of_row_eq_zero j hcol]

/-!
The stronger fact that, e.g., every totally-nonneg matrix stays totally-nonneg
under convex combinations, or the classical Lindström-Gessel-Viennot planar
interpretation of minors, is deferred. The definition of `TotallyNonneg` above
is already the standard one used in the amplituhedron / positive-Grassmannian
literature and suffices for downstream callers in the Paper93 pipeline.
-/

end PallLean.Paper93.DeepMath.Amplituhedron
