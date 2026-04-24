import PallLean.Paper93.DeepMath.NFrame.AdjugateFinTwo
import PallLean.Paper93.DeepMath.NFrame.AdjTraceBilinear

namespace PallLean.Paper93.DeepMath.NFrame

/-- 2×2 explicit Jacobi: `adjTraceAt A ΔA = A 1 1·ΔA 0 0 - A 0 1·ΔA 1 0 - A 1 0·ΔA 0 1 + A 0 0·ΔA 1 1`. -/
theorem adjTraceAt_fin_two_explicit (A ΔA : Matrix (Fin 2) (Fin 2) ℝ) :
    adjTraceAt A ΔA
      = A 1 1 * ΔA 0 0 - A 0 1 * ΔA 1 0 - A 1 0 * ΔA 0 1 + A 0 0 * ΔA 1 1 := by
  unfold adjTraceAt
  rw [adjugate_fin_two_eq]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.vecMul,
    Matrix.vecHead, Matrix.vecTail]
  ring

end PallLean.Paper93.DeepMath.NFrame
