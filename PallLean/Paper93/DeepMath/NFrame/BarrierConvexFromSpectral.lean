import PallLean.Paper93.DeepMath.NFrame.BarrierConvexHypothesis
import PallLean.Paper93.DeepMath.NFrame.EigenvectorUnitaryDet

namespace PallLean.Paper93.DeepMath.NFrame

/-- For PosDef A, there exists a diagonal matrix D and orthogonal U with
    `A = Uᵀ D U` and `det U² = 1`, so the barrier is invariant: `barrier A = barrier D`.

    For now we provide the existence statement: assuming we have such a decomposition. -/
theorem barrier_eq_diagonal_form_of_posDef {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (hSpec : hasSpectralDecomposition A) :
    ∃ D : Matrix (Fin n) (Fin n) ℝ, barrier A = barrier D := by
  exact barrier_eq_barrier_diagonal_of_spectral A (ne_of_gt hA.det_pos) hSpec

end PallLean.Paper93.DeepMath.NFrame
