import PallLean.Paper93.DeepMath.NFrame.SNF
import PallLean.Paper93.DeepMath.NFrame.SNFAlphaNonneg
import PallLean.Paper93.DeepMath.NFrame.ParityPenalty
import PallLean.Paper93.DeepMath.NFrame.Barrier

namespace PallLean.Paper93.DeepMath.NFrame

/-- The N-Frame Lagrangian S_NF is the sum of three terms with explicit decomposition. -/
theorem N_Frame_Lagrangian_three_term_form {n : ℕ} (α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    S_NF α β lam adj phi chi A
      = α * (∑ i, phi i * ((PallLean.Paper93.DeepMath.GraphSpectral.laplacian adj).mulVec phi) i)
      + β * parityPenalty chi phi
      + lam * (-Real.log A.det) := by
  rw [S_NF_decompose]
  unfold S_NF_alpha S_NF_beta S_NF_lambda barrier
  ring

end PallLean.Paper93.DeepMath.NFrame
