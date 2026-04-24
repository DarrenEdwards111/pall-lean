import PallLean.Paper93.DeepMath.NFrame.Barrier
import PallLean.Paper93.DeepMath.NFrame.DetFinOneFormulaCLM
import PallLean.Paper93.DeepMath.NFrame.FderivNegLog

namespace PallLean.Paper93.DeepMath.NFrame

open scoped Matrix.Norms.Elementwise

/-- For 1×1 matrices with `A 0 0 > 0`, the barrier `-log(det A) = -log(A 0 0)`
    has a Fréchet derivative at `A` (existence form). The derivative is
    morally `-1/(A 0 0) • proj 0 0`; here we package only existence and
    use `DifferentiableAt.hasFDerivAt` to extract a witness. -/
theorem barrier_hasFDerivAt_fin_one (A : Matrix (Fin 1) (Fin 1) ℝ) (h : 0 < A 0 0) :
    ∃ L : Matrix (Fin 1) (Fin 1) ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun M => barrier M) L A := by
  -- For 1×1 matrices, `det A = A 0 0`, so `det A > 0`.
  have h_det : A.det = A 0 0 := Matrix.det_fin_one A
  have h_pos : 0 < A.det := by rw [h_det]; exact h
  -- `Matrix.det` on 1×1 matrices is differentiable everywhere (it is the
  -- linear coordinate `A ↦ A 0 0`).
  have h_det_diff_at :
      DifferentiableAt ℝ (Matrix.det : Matrix (Fin 1) (Fin 1) ℝ → ℝ) A :=
    det_fin_one_differentiable.differentiableAt
  -- `Real.log` is differentiable at any nonzero point; here `det A > 0 ≠ 0`.
  have h_log_diff_at : DifferentiableAt ℝ Real.log A.det :=
    Real.differentiableAt_log (ne_of_gt h_pos)
  -- Composition: `M ↦ Real.log M.det` is differentiable at `A`.
  have h_logdet_diff_at :
      DifferentiableAt ℝ (fun M : Matrix (Fin 1) (Fin 1) ℝ => Real.log M.det) A :=
    h_log_diff_at.comp A h_det_diff_at
  -- Negation: `M ↦ -Real.log M.det = barrier M` is differentiable at `A`.
  have h_barrier_diff_at :
      DifferentiableAt ℝ (fun M : Matrix (Fin 1) (Fin 1) ℝ => barrier M) A := by
    have : DifferentiableAt ℝ
        (fun M : Matrix (Fin 1) (Fin 1) ℝ => -Real.log M.det) A :=
      h_logdet_diff_at.neg
    -- `barrier M = -Real.log M.det` definitionally.
    convert this using 1
  -- Extract the Fréchet derivative as a witness.
  exact ⟨fderiv ℝ (fun M => barrier M) A, h_barrier_diff_at.hasFDerivAt⟩

end PallLean.Paper93.DeepMath.NFrame
