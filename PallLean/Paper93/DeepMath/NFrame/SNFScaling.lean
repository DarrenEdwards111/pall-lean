import PallLean.Paper93.DeepMath.NFrame.SNF

namespace PallLean.Paper93.DeepMath.NFrame

/-- Scaling all three couplings by c ∈ ℝ multiplies S_NF by c. -/
theorem S_NF_coupling_scaling {n : ℕ} (c α β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    S_NF (c*α) (c*β) (c*lam) adj phi chi A = c * S_NF α β lam adj phi chi A := by
  unfold S_NF
  ring

/-- S_NF is linear in α (with β, λ fixed). -/
theorem S_NF_alpha_linear {n : ℕ} (α₁ α₂ β lam : ℝ)
    (adj : Matrix (Fin n) (Fin n) ℝ) (phi chi : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    S_NF (α₁ + α₂) β lam adj phi chi A
      = S_NF α₁ β lam adj phi chi A + S_NF α₂ 0 0 adj phi chi A := by
  unfold S_NF
  ring

end PallLean.Paper93.DeepMath.NFrame
