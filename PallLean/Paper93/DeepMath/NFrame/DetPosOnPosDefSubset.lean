import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# PosDef subset sits inside the positive-determinant subset

On real `n × n` matrices, positive definiteness implies positive
determinant.  Viewed set-theoretically, the locus of positive-definite
matrices is a subset of the locus of matrices with strictly positive
determinant:

* `posDef_det_pos_subset`:
  `{A | A.PosDef} ⊆ {A | 0 < A.det}`.
* `mem_posDef_imp_det_pos`: the membership-style rephrasing, taking an
  element of `{A | A.PosDef}` to `0 < A.det`.

Both statements are immediate consequences of
`Matrix.PosDef.det_pos` from Mathlib.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- The set `{A | A.PosDef}` is a subset of `{A | 0 < A.det}`. -/
theorem posDef_det_pos_subset {n : ℕ} :
    {A : Matrix (Fin n) (Fin n) ℝ | A.PosDef}
      ⊆ {A : Matrix (Fin n) (Fin n) ℝ | 0 < A.det} := by
  intros A hA
  exact hA.det_pos

/-- Rephrasing: PosDef ⇒ det > 0 (membership-style). -/
theorem mem_posDef_imp_det_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ {A : Matrix (Fin n) (Fin n) ℝ | A.PosDef}) :
    0 < A.det := hA.det_pos

end PallLean.Paper93.DeepMath.NFrame
