import PallLean.Paper93.DeepMath.NFrame.SNFAlphaDifferentiable

namespace PallLean.Paper93.DeepMath.NFrame

/-- The α-term of S_NF has a Fréchet derivative at every Φ — the linear form is
    implicit, derived from the quadratic form structure. -/
theorem S_NF_alpha_hasFDerivAt {n : ℕ} (α : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) :
    ∃ L : (Fin n → ℝ) →L[ℝ] ℝ,
      HasFDerivAt (fun psi => S_NF_alpha α A psi) L phi :=
  ⟨fderiv ℝ (fun psi => S_NF_alpha α A psi) phi,
    (S_NF_alpha_differentiable α A).differentiableAt.hasFDerivAt⟩

end PallLean.Paper93.DeepMath.NFrame
