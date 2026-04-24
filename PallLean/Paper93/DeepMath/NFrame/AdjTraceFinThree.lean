import PallLean.Paper93.DeepMath.NFrame.AdjTraceBilinear
import PallLean.Paper93.DeepMath.NFrame.DetFinThree

namespace PallLean.Paper93.DeepMath.NFrame

/-- 3×3 Jacobi structure: `adjTraceAt A ΔA = ∑_{ij} adj(A)_{ji} · ΔA_{ij}` (entrywise sum). -/
theorem adjTraceAt_fin_three_explicit (A ΔA : Matrix (Fin 3) (Fin 3) ℝ) :
    adjTraceAt A ΔA = (A.adjugate * ΔA).trace := rfl

/-- 3×3 explicit row-0 sum: `(adj A · ΔA).trace` expanded as Σⱼ adj(A) 0 j · ΔA j 0 + ... over all i. -/
theorem adjTraceAt_fin_three_sum_form (A ΔA : Matrix (Fin 3) (Fin 3) ℝ) :
    adjTraceAt A ΔA = ∑ i, ∑ j, A.adjugate i j * ΔA j i := by
  unfold adjTraceAt
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intros i _
  rw [Matrix.diag_apply, Matrix.mul_apply]

end PallLean.Paper93.DeepMath.NFrame
