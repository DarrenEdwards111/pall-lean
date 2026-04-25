import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Principal-TP structure of small explicit 2×2 matrices

This file enumerates the principal-TP structure of small explicit
matrices for `n = 2`. We give:

* The 2×2 identity matrix is principal-TP.
* The 2×2 diagonal matrix `diag(2, 3)` is principal-TP.
* For positive diagonal entries, the 2×2 diagonal matrix `diag(a, b)`
  is principal-TP.

These are the simplest examples of points lying in the strictly positive
locus (the "open positroid cell") of the principal-TNN cone for `n = 2`.

Since the in-flight file `DiagonalNonnegTNN.lean` is not yet built,
we prove a self-contained `diagonal_pos_isPrincipalTP` lemma inline
in this file: a diagonal real matrix with strictly positive entries is
principal-TP, since each principal minor is itself a diagonal matrix
whose determinant is a product of strictly positive entries.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- A diagonal matrix with strictly positive diagonal entries is
    principal-TP: every principal minor is a product of strictly
    positive entries, hence strictly positive. -/
theorem diagonal_pos_isPrincipalTP {n : ℕ} (d : Fin n → ℝ)
    (hd : ∀ i, 0 < d i) :
    IsPrincipalTP (Matrix.diagonal d) := by
  intro J
  -- The principal submatrix (indexed by `J` on both rows and columns)
  -- equals the diagonal matrix with entries `d ∘ Subtype.val`.
  have hInj : Function.Injective (fun i : J => (i.val : Fin n)) :=
    fun _ _ h => Subtype.ext h
  have h_sub :
      (Matrix.diagonal d).submatrix
          (fun i : J => (i.val : Fin n)) (fun j : J => (j.val : Fin n))
        = Matrix.diagonal (fun i : J => d i.val) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.submatrix_apply, Matrix.diagonal_apply_eq]
    · have hJij : (i.val : Fin n) ≠ j.val := fun heq => hij (hInj heq)
      simp [Matrix.submatrix_apply, Matrix.diagonal_apply_ne _ hJij,
            Matrix.diagonal_apply_ne _ hij]
  rw [h_sub, Matrix.det_diagonal]
  -- The determinant of the diagonal restriction is the product of
  -- `d i.val` over `i ∈ Finset.univ : Finset J`, which is a product of
  -- strictly positive reals, hence strictly positive.
  exact Finset.prod_pos (fun i _ => hd i.val)

/-- The 2×2 identity matrix is principal-TP. -/
theorem identity_2x2_isPrincipalTP :
    IsPrincipalTP (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  identity_isPrincipalTP 2

/-- The 2×2 diagonal matrix `diag(2, 3)` is principal-TP. -/
theorem diag_2_3_isPrincipalTP :
    IsPrincipalTP (Matrix.diagonal (![2, 3] : Fin 2 → ℝ)) := by
  apply diagonal_pos_isPrincipalTP
  intro i
  fin_cases i
  · -- d 0 = 2 > 0
    show (0 : ℝ) < 2
    norm_num
  · -- d 1 = 3 > 0
    show (0 : ℝ) < 3
    norm_num

/-- For 2×2 diagonal `diag(a, b)` with `a, b > 0`, principal-TP holds. -/
theorem diag_2x2_pos_isPrincipalTP (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IsPrincipalTP (Matrix.diagonal (![a, b] : Fin 2 → ℝ)) := by
  apply diagonal_pos_isPrincipalTP
  intro i
  fin_cases i
  · exact ha
  · exact hb

end PallLean.Paper93.DeepMath.PathB.Positroid
