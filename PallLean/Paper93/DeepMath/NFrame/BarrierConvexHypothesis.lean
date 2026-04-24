import PallLean.Paper93.DeepMath.NFrame.BarrierDiagonalConvex
import PallLean.Paper93.DeepMath.NFrame.BarrierViaEigenvalues
import PallLean.Paper93.DeepMath.NFrame.BarrierOrthogonalInvariant

/-!
# N-Frame: hypothesis-form spectral reduction for the barrier (Paper §28.3)

This file packages the spectral-decomposition reduction needed to lift
barrier convexity from the diagonal case to the PosDef case.

We do **not** prove that every PosDef matrix admits such a decomposition
here (that is a separate spectral-theorem development); instead, we
isolate the property as a `Prop` and show that whenever it holds for an
invertible matrix `A`, the barrier of `A` equals the barrier of the
diagonal factor `D`. This is the precise content needed to push
diagonal-orthant convexity through to PosDef in subsequent files.

Namespace: `PallLean.Paper93.DeepMath.NFrame`.
-/

namespace PallLean.Paper93.DeepMath.NFrame

/-- Spectral structure for PosDef as hypothesis: `A = Uᵀ D U` with
`(det U)² = 1` (orthogonal/unitary real) and `D` diagonal (off-diagonal
entries vanish). This packages a hypothetical spectral decomposition
without committing to a specific Mathlib spectral theorem. -/
def hasSpectralDecomposition {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ U D : Matrix (Fin n) (Fin n) ℝ,
    A = U.transpose * D * U ∧ U.det ^ 2 = 1 ∧ (∀ i j, i ≠ j → D i j = 0)

/-- If `A` has a spectral decomposition `A = Uᵀ D U` with `(det U)² = 1`
and `A` is invertible, then `barrier A = barrier D`. The proof uses
the orthogonal invariance of the barrier
(`barrier_conj_unit_det`) applied to the diagonal factor `D`. -/
theorem barrier_eq_barrier_diagonal_of_spectral {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0)
    (h : hasSpectralDecomposition A) :
    ∃ D : Matrix (Fin n) (Fin n) ℝ, barrier A = barrier D := by
  obtain ⟨U, D, hAUD, hUdet, _hDdiag⟩ := h
  refine ⟨D, ?_⟩
  -- Convert `U.det ^ 2 = 1` to `U.det * U.det = 1` for use with
  -- `barrier_conj_unit_det`.
  have hUmul : U.det * U.det = 1 := by
    have hsq : U.det ^ 2 = U.det * U.det := by ring
    rw [hsq] at hUdet
    exact hUdet
  -- We need `D.det ≠ 0` to invoke `barrier_conj_unit_det U D hUmul`.
  -- Since `A = Uᵀ D U` and `A.det ≠ 0`, multiplicativity of `det` and
  -- `det Uᵀ = det U` give `(det U)² · det D = det A`, so `det D ≠ 0`.
  have hDdet : D.det ≠ 0 := by
    intro hD0
    apply hA
    rw [hAUD]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hD0]
    ring
  -- Now apply orthogonal invariance to rewrite `barrier (Uᵀ D U)` as
  -- `barrier D`, then transport along `A = Uᵀ D U`.
  have hbar : barrier (U.transpose * D * U) = barrier D :=
    barrier_conj_unit_det U D hUmul hDdet
  rw [hAUD]
  exact hbar

end PallLean.Paper93.DeepMath.NFrame
