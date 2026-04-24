import PallLean.Paper93.DeepMath.NFrame.Barrier

namespace PallLean.Paper93.DeepMath.NFrame

/-- Barrier diverges to `+∞` as `det A → 0⁺`. Statement: for any K, there exists a
    det threshold δ > 0 such that `det A < δ ⇒ barrier A > K`. -/
theorem barrier_unbounded_as_det_to_zero {n : ℕ} (K : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Matrix (Fin n) (Fin n) ℝ, 0 < A.det → A.det < δ → K < barrier A := by
  -- barrier A = -log(det A). For det A < exp(-K-1), -log(det A) > K+1 > K.
  refine ⟨Real.exp (-(K + 1)), Real.exp_pos _, ?_⟩
  intros A hpos hlt
  unfold barrier
  have h1 : Real.log A.det < -(K + 1) := by
    have := Real.log_lt_log hpos hlt
    rwa [Real.log_exp] at this
  linarith

end PallLean.Paper93.DeepMath.NFrame
