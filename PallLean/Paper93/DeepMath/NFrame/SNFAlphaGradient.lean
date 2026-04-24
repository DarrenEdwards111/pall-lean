import PallLean.Paper93.DeepMath.NFrame.SNFAlphaDifferentiable
import PallLean.Paper93.DeepMath.NFrame.SNF

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.GraphSpectral

/-- α-term is FDeriv-differentiable, as previously established. Re-export for discoverability. -/
theorem S_NF_alpha_differentiable_at {n : ℕ} (α : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) :
    DifferentiableAt ℝ (fun psi => S_NF_alpha α A psi) phi :=
  S_NF_alpha_differentiable α A phi

/-- Evaluation of the α-term at zero: `S_NF_alpha α A 0 = 0`. -/
theorem S_NF_alpha_zero_eq {n : ℕ} (α : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    S_NF_alpha α A (0 : Fin n → ℝ) = 0 := by
  unfold S_NF_alpha
  simp [Matrix.mulVec_zero, Finset.sum_const_zero, mul_zero]

end PallLean.Paper93.DeepMath.NFrame
