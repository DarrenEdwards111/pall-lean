import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.NFrame.DetDifferentiable

/-!
# Continuity of the N-Frame barrier on `{det > 0}` (paper §28.3)

This file establishes that the single-minor log-det barrier
`barrier A := -Real.log (det A)` is continuous on the open set
`{A | 0 < A.det}` of real `n × n` matrices with positive determinant.

The proof composes:

* `det_differentiable.continuous` — continuity of the determinant,
  obtained from the permutation-sum expansion `Matrix.det_apply` in
  `DetDifferentiable.lean`;
* `ContinuousOn.log` — continuity of `Real.log ∘ f` on a set where
  `f ≠ 0`;
* `ContinuousOn.neg` — negation preserves continuity on sets;
* `isOpen_lt` — the strict inequality set `{A | 0 < A.det}` is open as
  a preimage under a pair of continuous functions.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- `barrier = -Real.log ∘ Matrix.det` is continuous on the set `{A | 0 < A.det}`. -/
theorem barrier_continuousOn_det_pos {n : ℕ} :
    ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℝ => barrier A)
                 {A : Matrix (Fin n) (Fin n) ℝ | 0 < A.det} := by
  unfold barrier
  apply ContinuousOn.neg
  apply ContinuousOn.log
  · exact det_differentiable.continuous.continuousOn
  · intros A hA
    exact ne_of_gt hA

/-- On the open subset `{A | 0 < A.det}`, each point is interior and barrier is
    continuous there. -/
theorem barrier_continuousAt_of_det_pos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (h : 0 < A.det) :
    ContinuousAt (fun B => barrier B) A := by
  have hA : A ∈ {B : Matrix (Fin n) (Fin n) ℝ | 0 < B.det} := h
  have hopen : IsOpen {B : Matrix (Fin n) (Fin n) ℝ | 0 < B.det} := by
    exact isOpen_lt continuous_const det_differentiable.continuous
  exact (barrier_continuousOn_det_pos A hA).continuousAt (hopen.mem_nhds hA)

end PallLean.Paper93.DeepMath.NFrame
