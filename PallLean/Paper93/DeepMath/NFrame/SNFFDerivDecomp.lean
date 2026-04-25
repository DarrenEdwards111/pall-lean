import PallLean.Paper93.DeepMath.NFrame.SNFAlphaDifferentiable
import PallLean.Paper93.DeepMath.NFrame.SNFLambdaDifferentiable

namespace PallLean.Paper93.DeepMath.NFrame

/-- The α-term FDeriv at a point Φ is well-defined. -/
theorem S_NF_alpha_fderiv_well_defined {n : ℕ} (α : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (phi : Fin n → ℝ) :
    ∃ L : (Fin n → ℝ) →L[ℝ] ℝ, fderiv ℝ (fun psi => S_NF_alpha α A psi) phi = L :=
  ⟨fderiv ℝ (fun psi => S_NF_alpha α A psi) phi, rfl⟩

/-- The λ-term FDeriv at a PosDef matrix A is well-defined. -/
theorem S_NF_lambda_fderiv_well_defined {n : ℕ} (lam : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ∃ L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun M => S_NF_lambda lam M) L A :=
  ⟨fderiv ℝ (fun M => S_NF_lambda lam M) A,
   (S_NF_lambda_differentiableAt_posDef lam A hA).hasFDerivAt⟩

end PallLean.Paper93.DeepMath.NFrame
