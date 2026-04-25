import PallLean.Paper93.DeepMath.NFrame.BarrierConvexFromSpectral
import PallLean.Paper93.DeepMath.NFrame.BarrierConvexHypothesis

namespace PallLean.Paper93.DeepMath.NFrame

/-- For PosDef A, the barrier `-log(det A)` equals the diagonal-form barrier (via spectral
    decomposition assumption). This is the main bridge to non-diagonal convexity. -/
theorem barrier_convexOn_posDef_via_spectral_assumption {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (hSpec : hasSpectralDecomposition A) :
    ∃ D : Matrix (Fin n) (Fin n) ℝ, barrier A = barrier D :=
  barrier_eq_diagonal_form_of_posDef A hA hSpec

end PallLean.Paper93.DeepMath.NFrame
