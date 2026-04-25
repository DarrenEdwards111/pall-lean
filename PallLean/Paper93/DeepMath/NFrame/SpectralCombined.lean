import PallLean.Paper93.DeepMath.NFrame.PosDefSpectralStrong
import PallLean.Paper93.DeepMath.NFrame.BarrierConvexHypothesis
import PallLean.Paper93.DeepMath.NFrame.BarrierOrthogonalInvariant

namespace PallLean.Paper93.DeepMath.NFrame

open scoped Matrix

/-- For PosDef A, the eigenvector unitary U from Mathlib is orthogonal (UᵀU = 1),
    and `barrier(Uᵀ A U) = barrier A` whenever `A.det ≠ 0`. -/
theorem posDef_barrier_invariant_under_eigvec_unitary {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ, Uᵀ * U = 1 ∧
      barrier (Uᵀ * A * U) = barrier A := by
  obtain ⟨U, hU⟩ := posDef_eigenvectorUnitary_orthogonal A hA
  refine ⟨U, hU, ?_⟩
  apply barrier_conj_unit_det
  · -- need: U.det * U.det = 1, derive from Uᵀ * U = 1 (det Uᵀ * det U = 1, det Uᵀ = det U)
    have h := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    exact h
  · exact ne_of_gt hA.det_pos

end PallLean.Paper93.DeepMath.NFrame
