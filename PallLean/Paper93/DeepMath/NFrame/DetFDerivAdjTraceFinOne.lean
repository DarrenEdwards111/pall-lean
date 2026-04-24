import PallLean.Paper93.DeepMath.NFrame.DetFinOneFormulaCLM
import PallLean.Paper93.DeepMath.NFrame.AdjTraceLinearMap

namespace PallLean.Paper93.DeepMath.NFrame

open scoped Matrix.Norms.Elementwise

/-- For 1×1 matrices: det's Fréchet derivative at A applied to ΔA equals adjTraceAt A ΔA.
    (Verifies the Jacobi formula at n = 1.) -/
theorem detFinOneCLM_eq_adjTraceAt (A ΔA : Matrix (Fin 1) (Fin 1) ℝ) :
    detFinOneCLM ΔA = adjTraceAt A ΔA := by
  unfold detFinOneCLM adjTraceAt
  -- detFinOneCLM ΔA = ΔA 0 0; adjTraceAt A ΔA = trace(adj A · ΔA) = adj(A) 0 0 · ΔA 0 0
  -- For 1×1, adj(A) 0 0 = 1 (Matrix.adjugate_fin_one)
  rw [Matrix.adjugate_fin_one]
  show ΔA 0 0 = ((1 : Matrix (Fin 1) (Fin 1) ℝ) * ΔA).trace
  rw [Matrix.one_mul]
  simp [Matrix.trace]

end PallLean.Paper93.DeepMath.NFrame
