import PallLean.Paper93.DeepMath.NFrame.BarrierContinuous

namespace PallLean.Paper93.DeepMath.NFrame

/-- The set `{A | c ≤ A.det ∧ A.det ≤ C}` for positive `c, C` is closed (preimage of `[c, C]`
    under continuous `det`). -/
theorem isClosed_det_interval {n : ℕ} (c C : ℝ) :
    IsClosed {A : Matrix (Fin n) (Fin n) ℝ | c ≤ A.det ∧ A.det ≤ C} := by
  have h1 : IsClosed {A : Matrix (Fin n) (Fin n) ℝ | c ≤ A.det} :=
    isClosed_le continuous_const det_differentiable.continuous
  have h2 : IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.det ≤ C} :=
    isClosed_le det_differentiable.continuous continuous_const
  exact h1.inter h2

end PallLean.Paper93.DeepMath.NFrame
