import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.NFrame.DetDifferentiable

/-!
# Continuity of the N-Frame barrier on `{A | 0 < det A}`

We show that the single-minor log-det barrier
`B(A) := -log(det A)` from `PallLean.Paper93.DeepMath.NFrame.Barrier`
is continuous on the open set `{A | 0 < A.det}`.

This is obtained by combining the (global) continuity of
`Matrix.det` (derived from `det_differentiable` in
`DetDifferentiable.lean`), continuity of `Real.log` on the positive
reals, and negation continuity.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- `barrier A = -Real.log (det A)` is continuous on the open locus
    `{A | 0 < A.det}` of matrices with positive determinant. -/
theorem barrier_continuousOn_det_pos {n : ℕ} :
    ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℝ => barrier A)
                 {A : Matrix (Fin n) (Fin n) ℝ | 0 < A.det} := by
  unfold barrier
  -- `barrier A = -(Real.log (det A))`.  We show continuity of
  -- `Real.log ∘ det` first, then apply `ContinuousOn.neg`.
  refine ContinuousOn.neg ?_
  -- `log ∘ det` is continuous on `{0 < det}` because
  -- (i) `det` is continuous everywhere (via `det_differentiable`),
  -- (ii) `Real.log` is continuous at every nonzero real, and
  -- (iii) on `{0 < det}` the value `det A` is nonzero.
  have hdet : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℝ => A.det)
      {A : Matrix (Fin n) (Fin n) ℝ | 0 < A.det} :=
    det_differentiable.continuous.continuousOn
  refine ContinuousOn.log hdet ?_
  intro A hA
  exact ne_of_gt hA

/-- `barrier` is continuous at every matrix `A` with `0 < det A`. -/
theorem barrier_continuousAt_of_det_pos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : 0 < A.det) :
    ContinuousAt (fun M : Matrix (Fin n) (Fin n) ℝ => barrier M) A := by
  -- Since `{M | 0 < det M}` is open and `barrier` is continuous on it, we
  -- conclude pointwise `ContinuousAt` at any interior point.
  have hopen : IsOpen {M : Matrix (Fin n) (Fin n) ℝ | 0 < M.det} := by
    -- Preimage of the open set `(0, ∞) ⊆ ℝ` under the continuous map `det`.
    have hdet_cont : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M.det) :=
      det_differentiable.continuous
    exact hdet_cont.isOpen_preimage _ isOpen_Ioi
  have hmem : A ∈ {M : Matrix (Fin n) (Fin n) ℝ | 0 < M.det} := hA
  exact (barrier_continuousOn_det_pos A hmem).continuousAt (hopen.mem_nhds hmem)

end PallLean.Paper93.DeepMath.NFrame
