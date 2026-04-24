import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Basic

/-!
# Adjugate-trace bilinear form (N-Frame)

We package the "Jacobi" candidate linear functional `ΔA ↦ tr(adj(A) · ΔA)`
as `adjTraceAt A`, and prove its additivity and scalar-homogeneity in
`ΔA`. This is the building block identifying `adjTraceAt A` with the
Fréchet derivative of `det` at `A` in the later Jacobi-formula chain.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Trace of adj(A) · M expanded explicitly. This is the candidate "Jacobi" linear functional. -/
def adjTraceAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ΔA : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (A.adjugate * ΔA).trace

/-- adjTraceAt is additive in ΔA. -/
theorem adjTraceAt_add {n : ℕ} (A ΔA ΔB : Matrix (Fin n) (Fin n) ℝ) :
    adjTraceAt A (ΔA + ΔB) = adjTraceAt A ΔA + adjTraceAt A ΔB := by
  unfold adjTraceAt
  rw [Matrix.mul_add, Matrix.trace_add]

/-- adjTraceAt scales linearly in ΔA. -/
theorem adjTraceAt_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (ΔA : Matrix (Fin n) (Fin n) ℝ) :
    adjTraceAt A (c • ΔA) = c * adjTraceAt A ΔA := by
  unfold adjTraceAt
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- At A = 0 (trivial case), adjTraceAt A ΔA may be zero (degenerate). -/
theorem adjTraceAt_zero_matrix {n : ℕ} (hn : 1 ≤ n) :
    adjTraceAt (0 : Matrix (Fin n) (Fin n) ℝ) 0 = 0 := by
  unfold adjTraceAt
  simp

end PallLean.Paper93.DeepMath.NFrame
