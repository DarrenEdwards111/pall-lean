import PallLean.Paper93.DeepMath.NFrame.SNFAlphaDifferentiable

namespace PallLean.Paper93.DeepMath.NFrame

/-- The α-term is differentiable everywhere (existence of FDeriv). -/
theorem S_NF_alpha_differentiable_everywhere {n : ℕ} (α : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) :
    ∃ L : (Fin n → ℝ) →L[ℝ] ℝ,
      HasFDerivAt (fun psi : Fin n → ℝ => S_NF_alpha α A psi) L phi :=
  ⟨fderiv ℝ (fun psi : Fin n → ℝ => S_NF_alpha α A psi) phi,
    (S_NF_alpha_differentiable α A).differentiableAt.hasFDerivAt⟩

end PallLean.Paper93.DeepMath.NFrame
