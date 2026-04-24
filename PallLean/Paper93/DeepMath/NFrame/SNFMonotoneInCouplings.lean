import PallLean.Paper93.DeepMath.NFrame.SNF

namespace PallLean.Paper93.DeepMath.NFrame

open PallLean.Paper93.DeepMath.GraphSpectral

/-- If `α ≤ α'`, `β = β'`, `λ = λ'`, and α-term ≥ 0, then `S_NF α ≤ S_NF α'`. -/
theorem S_NF_monotone_in_alpha {n : ℕ} (α α' β lam : ℝ) (hα : α ≤ α')
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hterm : 0 ≤ ∑ i, phi i * ((laplacian adj).mulVec phi i)) :
    S_NF α β lam adj phi chi A ≤ S_NF α' β lam adj phi chi A := by
  unfold S_NF
  have hmul : α * (∑ i, phi i * ((laplacian adj).mulVec phi i))
      ≤ α' * (∑ i, phi i * ((laplacian adj).mulVec phi i)) :=
    mul_le_mul_of_nonneg_right hα hterm
  linarith

end PallLean.Paper93.DeepMath.NFrame
