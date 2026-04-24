import PallLean.Paper93.DeepMath.NFrame.DetDifferentiable

/-!
# Openness of the positive-determinant and nonzero-determinant loci

We show that the subset `{A | 0 < A.det}` of the space of real square
matrices is open, as well as the larger subset `{A | A.det ≠ 0}`.
Both are obtained from continuity of `Matrix.det` (inherited from its
differentiability proved in
`PallLean.Paper93.DeepMath.NFrame.DetDifferentiable`).

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- The set `{A | 0 < A.det}` is open in the space of matrices (preimage of
    `(0, ∞)` under the continuous determinant map). -/
theorem isOpen_det_pos {n : ℕ} :
    IsOpen {A : Matrix (Fin n) (Fin n) ℝ | 0 < A.det} := by
  exact isOpen_lt continuous_const det_differentiable.continuous

/-- The set `{A | A.det ≠ 0}` is open: it is the preimage under the continuous
    map `A ↦ A.det` of the open set `{x : ℝ | x ≠ 0}` (which is open because
    `ℝ` is a `T1Space`). -/
theorem isOpen_det_ne_zero {n : ℕ} :
    IsOpen {A : Matrix (Fin n) (Fin n) ℝ | A.det ≠ 0} := by
  have h : {A : Matrix (Fin n) (Fin n) ℝ | A.det ≠ 0}
      = (fun A : Matrix (Fin n) (Fin n) ℝ => A.det) ⁻¹' {x : ℝ | x ≠ 0} := rfl
  rw [h]
  exact (isOpen_ne (x := (0 : ℝ))).preimage det_differentiable.continuous

end PallLean.Paper93.DeepMath.NFrame
