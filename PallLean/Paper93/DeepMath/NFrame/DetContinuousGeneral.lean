import PallLean.Paper93.DeepMath.NFrame.DetDifferentiable

namespace PallLean.Paper93.DeepMath.NFrame

/-- `Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ` is continuous (everywhere). -/
theorem det_continuous {n : ℕ} :
    Continuous (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) :=
  det_differentiable.continuous

/-- The preimage of any open set under Matrix.det is open. -/
theorem det_preimage_open {n : ℕ} {s : Set ℝ} (hs : IsOpen s) :
    IsOpen ((Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) ⁻¹' s) :=
  hs.preimage det_continuous

end PallLean.Paper93.DeepMath.NFrame
