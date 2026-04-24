import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.NFrame.DetDifferentiable
import PallLean.Paper93.DeepMath.NFrame.DetPosOpen
import Mathlib.Analysis.Matrix.PosDef

/-!
# Differentiability of the N-Frame barrier `B(A) = -log(det A)`

This file establishes that the single-minor barrier
`barrier A := -log(det A)` is Fréchet differentiable at any matrix
`A : Matrix (Fin n) (Fin n) ℝ` whose determinant is nonzero. The
proof composes:

* `det_differentiable` (from `DetDifferentiable.lean`): the determinant
  is differentiable everywhere on `Matrix (Fin n) (Fin n) ℝ`;
* `Real.differentiableAt_log`: the natural logarithm is differentiable
  at any nonzero real number;
* the chain rule (`DifferentiableAt.comp`) and negation
  (`DifferentiableAt.neg`).

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

open scoped Matrix.Norms.Elementwise

namespace PallLean.Paper93.DeepMath.NFrame

/-- The barrier `B(A) = -log(det A)` is Fréchet differentiable at any
matrix `A` with `det A ≠ 0`. -/
theorem barrier_differentiableAt_of_det_ne_zero
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : A.det ≠ 0) :
    DifferentiableAt ℝ (fun M : Matrix (Fin n) (Fin n) ℝ => barrier M) A := by
  -- `Matrix.det` is differentiable everywhere; specialise to `A`.
  have h_det_diff_at :
      DifferentiableAt ℝ
        (fun M : Matrix (Fin n) (Fin n) ℝ => M.det) A :=
    det_differentiable.differentiableAt
  -- `Real.log` is differentiable at any nonzero real number; in
  -- particular at `A.det`.
  have h_log_diff_at : DifferentiableAt ℝ Real.log A.det :=
    Real.differentiableAt_log h
  -- Compose: `M ↦ Real.log M.det` is differentiable at `A`.
  have h_logdet_diff_at :
      DifferentiableAt ℝ
        (fun M : Matrix (Fin n) (Fin n) ℝ => Real.log M.det) A :=
    h_log_diff_at.comp A h_det_diff_at
  -- Negate: `M ↦ -Real.log M.det = barrier M` is differentiable at `A`.
  have h_neg_logdet_diff_at :
      DifferentiableAt ℝ
        (fun M : Matrix (Fin n) (Fin n) ℝ => -Real.log M.det) A :=
    h_logdet_diff_at.neg
  -- `barrier M = -Real.log M.det` definitionally.
  exact h_neg_logdet_diff_at

/-- Barrier is differentiable at any positive definite matrix.

A positive definite real matrix has strictly positive determinant
(`Matrix.PosDef.det_pos`), so in particular `det A ≠ 0`, and we can
invoke `barrier_differentiableAt_of_det_ne_zero`. -/
theorem barrier_differentiableAt_posDef
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    DifferentiableAt ℝ (fun M : Matrix (Fin n) (Fin n) ℝ => barrier M) A :=
  barrier_differentiableAt_of_det_ne_zero A (ne_of_gt hA.det_pos)

end PallLean.Paper93.DeepMath.NFrame
